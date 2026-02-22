--[[
    delay-histogram.lua: Automatically tune the delay threshold using a
        histogram and smooth out major speed resets

    Copyright (C) 2022
        Charles Corrigan mailto:chas-iot@runegate.org (github @chas-iot)

    This Source Code Form is subject to the terms of the Mozilla Public
    License, v. 2.0. If a copy of the MPL was not distributed with this
    file, You can obtain one at https://mozilla.org/MPL/2.0/.


    Covered Software is provided under this License on an "as is"
    basis, without warranty of any kind, either expressed, implied, or
    statutory, including, without limitation, warranties that the
    Covered Software is free of defects, merchantable, fit for a
    particular purpose or non-infringing. The entire risk as to the
    quality and performance of the Covered Software is with You.
    Should any Covered Software prove defective in any respect, You
    (not any Contributor) assume the cost of any necessary servicing,
    repair, or correction. This disclaimer of warranty constitutes an
    essential part of this License. No use of any Covered Software is
    authorized under this License except under this disclaimer.

]]
--
--
-- Inspired by comments from @dlakelan on how to tune the delay threshold
-- The delay threshold should be calculated from the baseline latency
-- from 5 to 10 minutes of of a quiet network
--
-- This module attempts to do this by collecting latencies from when the
-- network load is low to create a histogram. Once sufficient values are
-- collected, the delay threshold is set to a cut-off value from the
-- histogram at a specified ratio to the cumulative count of readings.
--
-- Using the histogram, also smooth out rate controller 'speed resets' to
-- minimum speeds. A speed reset is when the main loop detects a high
-- delay at the same time as a low load. Use the histogram data to detect
-- if the delay appears to be transient (i.e. low occurrence count) and,
-- if so mitigate the reset
--
-- The histogram is a two level structure of delay
-- counts.
-- At the outer level, there are _5_ histograms         -- number_of_histograms
--
-- Each histogram is an array of millisecond counts,
-- with the _lowest_ and                                -- min_allowed_threshold
-- and the _highest_ buckets containing aggregate       -- max_allowed_threshold
-- counts for all delays below and above the
-- respective cutoffs
--
-- Every tick updates all histograms
--
-- Every _1/2 hour_, the 'next' histogram is zeroed out -- histogram_offset_seconds
--
-- When it is _time_ to calculate the delay threshold,  -- recalculation_seconds
-- the histogram with the largest readings count is
-- chosen so that after the initial long startup, the
-- delay threshold is calculated from 3-3.5 hours of
-- readings
--
-- If there are _too few low load readings_,            -- sufficient_seconds, sufficient_readings_count
-- particularly during early startup, then use the
-- default delay thresholds from the external settings
--
-- To calculate the new delay threshold, process the
-- histogram to find the lowest delay such that the
-- cumulative count is greater than or equal to a
-- specified cuttoff                                    -- cumulative_cutoff
--
-- Low load is determined either in 'relative' or       -- use_relative_low_load
-- 'absolute` terms.
--
-- If absolute, then _low load_ is when the current
-- utilisation is less than the minimum speed
-- currently calculated from a percentage of the
-- maximum (likely to change)
--
-- If relative, then low load is when the current
-- utilisation relative to the current speed is less
-- than a configured value                              -- low_load_threshold
--
-- The tunables and assumptions may be overridden in /etc/config/sqm-autorate
-- in a section named `delay_histogram` (not delay-histogram)
--[[
config delay_histogram
#       option cumulative_cutoff '0.9994'
        option low_load_type 'absolute'
]]
--
-- The settings available are
--      histogram_offset_seconds
--      number_of_histograms
--      low_load_threshold
--      sufficient_seconds
--      recalculation_seconds
--      cumulative_cutoff
--      histogram_log_level
--      low_load_type
--


--==--==--==-- begin public interface --==--==--==--
local M = {}

M.name = 'delay-histogram'

-- function pre_process(readings)
--  Phase 1: called BEFORE rate decisions
--  Collects histogram data and recalculates delay thresholds
--  parameters
--      readings    -- table of readings values from main
--  returns
--      results     -- table with ul_max_delta_owd and dl_max_delta_owd (or empty)
M.pre_process = nil

-- function process(readings)
--  Phase 2: called AFTER rate decisions
--  Handles speed reset mitigation only
--  parameters
--      readings    -- table of readings values from main
--  returns
--      results     -- table of results
M.process = nil


-- function initialise(requires, settings)
--  parameters
--      requires    -- table of requires from main
--      settings    -- table of settings values from main
--  returns
--      M           -- the module, for a fluent interface
M.initialise = nil


--==--==--==-- end public interface --==--==--==--

-- tunable values and assumptions (constants)
local histogram_log_level = 'INFO'       -- the log level to report the histogram
local histogram_offset_seconds = 30 * 60 -- 1/2 hour
local number_of_histograms = 5           -- 5 buckets - so each bucket contains up to 2.5 hours given the offset above
-- from 2.5 hours after startup, there will be 2 to 2.5 hours of data in
-- the 'oldest' histogram
-- every 30 mins, the 'oldest' will be initialised to counts of
-- 0 to become the latest
local low_load_threshold = 0.20      -- below this relative load factor, the network is not busy
local sufficient_seconds = 60 * 10   -- 10 minutes of low load
local recalculation_seconds = 60 * 5 -- recalculate the delay threshold every 5 minutes
local cumulative_cutoff = 0.9995     -- cumulative cutoff ratio for the delay threshold, allows 1/2000 above cutoff
local min_allowed_threshold = 1      -- below this does not bring much benefit
local max_allowed_threshold = 39     -- VOIP protocols have a 20ms cycle, it's not good to be more than twice that
local use_relative_low_load = false  -- low load can be measure in relative (tx_load, rx_load, compared to
-- low_load_threshold) or absolute (up_utilsation, down_utilisation, compared
-- to min_ul_rate, min_dl_rate) terms
-- end of tunables and assumptions

-- values (constants) to be set in M.initialise from settings
local sufficient_readings_count = nil -- calculated from sufficient_seconds above

-- utility functions to setup or import in M.initialise
local limit
local floor
local ceil
local logger
local loglevel
local util

-- Per-direction state: each entry bundles histogram data, thresholds, and reading key mappings
local directions = {} -- populated in M.initialise

local histogram_start_time = {}   -- the time the histogram was initialised, for reporting

local latest_histogram_no = 0     -- deliberately invalid for first pass - lua arrays generally start from 1

local last_recalculated_time = 90 -- start the first recalculation 90s later, to allow for initialisation

local first_run = false

local function make_direction(config)
    return {
        histogram = {},           -- [histogram_no] = array of delay counts
        count = {},               -- [histogram_no] = total readings count
        result_prev = 0,          -- previous threshold result for change detection
        threshold_default = config.threshold_default, -- fallback when insufficient data
        min_speed = config.min_speed,                 -- minimum speed for absolute low-load check
        label = config.label,                         -- display label ("UP  " or "DOWN")
        -- Reading key mappings (keys into the readings table)
        load_key = config.load_key,                   -- "tx_load" or "rx_load"
        utilisation_key = config.utilisation_key,      -- "up_utilisation" or "down_utilisation"
        del_stat_key = config.del_stat_key,            -- "up_del_stat" or "down_del_stat"
        next_rate_key = config.next_rate_key,          -- "next_ul_rate" or "next_dl_rate"
        cur_rate_key = config.cur_rate_key,            -- "cur_ul_rate" or "cur_dl_rate"
        -- Result key mappings (keys in the results table)
        threshold_result_key = config.threshold_result_key, -- "ul_max_delta_owd" or "dl_max_delta_owd"
        good_count_key = config.good_count_key,             -- "upload_good_count" or "download_good_count"
        good_count = false,       -- whether histogram has sufficient data for this direction
    }
end

local function initialise_histogram(new_histogram, now)
    -- initialise the new slot
    histogram_start_time[new_histogram] = now

    for _, dir in ipairs(directions) do
        dir.histogram[new_histogram] = {}
        dir.count[new_histogram] = 0
        local t = dir.histogram[new_histogram]
        for i = min_allowed_threshold, max_allowed_threshold do
            t[i] = 0
        end
    end

    if first_run then
        logger(histogram_log_level, "delay histogram - abbreviations - s: seconds;  ms: milliseconds of delay;  " ..
            "#: count;  p: proportion of total; c: cumulative proportion")
        first_run = false
    end

    return new_histogram
end


function M.initialise(requires, settings)
    local math = requires.math
    floor = math.floor
    ceil = math.ceil
    local min = math.min
    local max = math.max
    limit = function(value, allowed_min, allowed_max)
        return min(max(value, allowed_min), allowed_max)
    end

    util = requires.util
    logger = util.logger
    loglevel = util.loglevel
    histogram_log_level = loglevel[histogram_log_level] -- get the correct logging structure

    -- Create per-direction state
    directions = {
        make_direction({
            threshold_default = settings.ul_max_delta_owd,
            min_speed = settings.min_ul_rate,
            label = "UP  ",
            load_key = "tx_load",
            utilisation_key = "up_utilisation",
            del_stat_key = "up_del_stat",
            next_rate_key = "next_ul_rate",
            cur_rate_key = "cur_ul_rate",
            threshold_result_key = "ul_max_delta_owd",
            good_count_key = "upload_good_count",
        }),
        make_direction({
            threshold_default = settings.dl_max_delta_owd,
            min_speed = settings.min_dl_rate,
            label = "DOWN",
            load_key = "rx_load",
            utilisation_key = "down_utilisation",
            del_stat_key = "down_del_stat",
            next_rate_key = "next_dl_rate",
            cur_rate_key = "cur_dl_rate",
            threshold_result_key = "dl_max_delta_owd",
            good_count_key = "download_good_count",
        }),
    }

    for _, dir in ipairs(directions) do
        dir.result_prev = dir.threshold_default
    end

    -- load UCI settings (if any)
    if settings.plugin then
        local plugin_settings = settings.plugin("delay_histogram")
        local string_table = {}
        string_table[1] = "delay-histogram - settings:"
        if plugin_settings then
            if plugin_settings.histogram_offset_seconds then
                histogram_offset_seconds = util.to_integer(plugin_settings.histogram_offset_seconds)
                string_table[#string_table + 1] = "histogram_offset_seconds=" .. tostring(histogram_offset_seconds)
            end
            if plugin_settings.number_of_histograms then
                number_of_histograms = util.to_integer(plugin_settings.number_of_histograms)
                string_table[#string_table + 1] = "number_of_histograms=" .. tostring(number_of_histograms)
            end
            if plugin_settings.low_load_threshold then
                low_load_threshold = tonumber(plugin_settings.low_load_threshold, 10)
                string_table[#string_table + 1] = "low_load_threshold=" .. tostring(low_load_threshold)
            end
            if plugin_settings.sufficient_seconds then
                sufficient_seconds = util.to_integer(plugin_settings.sufficient_seconds)
                string_table[#string_table + 1] = "sufficient_seconds=" .. tostring(sufficient_seconds)
            end
            if plugin_settings.recalculation_seconds then
                recalculation_seconds = util.to_integer(plugin_settings.recalculation_seconds)
                string_table[#string_table + 1] = "recalculation_seconds=" .. tostring(recalculation_seconds)
            end
            if plugin_settings.cumulative_cutoff then
                cumulative_cutoff = tonumber(plugin_settings.cumulative_cutoff, 10)
                string_table[#string_table + 1] = "cumulative_cutoff=" .. tostring(cumulative_cutoff)
            end
            if plugin_settings.histogram_log_level then
                histogram_log_level = plugin_settings.histogram_log_level
                string_table[#string_table + 1] = "histogram_log_level=" .. histogram_log_level
                histogram_log_level = loglevel[histogram_log_level]
            end
            if plugin_settings.low_load_type then
                if plugin_settings.low_load_type == 'relative' then
                    use_relative_low_load = true
                elseif plugin_settings.low_load_type == 'absolute' then
                    use_relative_low_load = false
                end
                string_table[#string_table + 1] = "use_relative_low_load=" .. tostring(use_relative_low_load)
            end
            if #string_table > 1 then
                logger(loglevel.WARN, table.concat(string_table, "\n        "))
            end
        end
    end

    sufficient_readings_count = ceil(sufficient_seconds / settings.tick_duration)

    for i = 1, number_of_histograms do
        initialise_histogram(i, 0)
    end

    first_run = true

    -- return the module
    return M
end

local function print_histogram(histogram_no, dir_highlights, now)
    -- shows the calculated delay in relation to the histogram
    -- dir_highlights[i] corresponds to directions[i]
    local decorate = function(i, level)
        if i < level then
            return '|'
        elseif i == level then
            return '+-'
        else
            return ''
        end
    end

    -- create a table of strings, it's much faster to concatenate with table.concat than repeatedly with `..`
    local string_table = {}
    string_table[1] = "delay histogram"

    for idx, dir in ipairs(directions) do
        local histogram = dir.histogram[histogram_no]
        local total = dir.count[histogram_no]
        local highlight = dir_highlights[idx]
        if total > 0 then
            local count = 0
            string_table[#string_table + 1] = string.format(
                "%4s    s: %5d  #: %5d",
                dir.label, (now - histogram_start_time[histogram_no]), total)
            for j = min_allowed_threshold, max_allowed_threshold do
                count = count + histogram[j]
                if histogram[j] > 0 or j == highlight then
                    string_table[#string_table + 1] = string.format(
                        "ms: %2d  #: %5d  p: %.6f  c: %.6f %s",
                        j, histogram[j], histogram[j] / total, count / total, decorate(j, highlight))
                end
            end
        end
    end

    logger(histogram_log_level, table.concat(string_table, "\n    "))
end


local function calculate_thresholds(histogram_no, print_it, now)
    local results = {}

    local function calc_threshold(histogram, total)
        local result = nil

        -- don't bother if there are too few readings
        if total > sufficient_readings_count then
            -- find the cut-off point
            local target = total * cumulative_cutoff
            local count = 0
            for j = min_allowed_threshold, max_allowed_threshold do
                count = count + histogram[j]
                if count >= target then
                    result = j
                    break
                end
            end
            if result == nil then
                logger(loglevel.WARN, "delay-histogram plugin: X_max_delta_owd is nil")
                result = max_allowed_threshold
            end

            result = limit and limit(result, min_allowed_threshold, max_allowed_threshold)

            -- a heuristic in case of relatively low counts (eg. during the long initial build of the histogram)
            -- find the lowest bucket with a count > 1
            if histogram[result] == 1 then
                for i = result - 1, min_allowed_threshold, -1 do
                    if histogram[i] > 1 then
                        result = i
                        break
                    end
                end
            end
        end
        return result
    end

    local dir_highlights = {}
    local threshold_changed = false

    for idx, dir in ipairs(directions) do
        local delay_threshold = calc_threshold(dir.histogram[histogram_no], dir.count[histogram_no])
        if delay_threshold then
            dir.good_count = true
            results[dir.good_count_key] = true
        else
            delay_threshold = dir.threshold_default
            dir.good_count = false
        end
        dir_highlights[idx] = delay_threshold
        results[dir.threshold_result_key] = delay_threshold

        if delay_threshold ~= dir.result_prev then
            threshold_changed = true
        end
        dir.result_prev = util.to_integer(delay_threshold)
    end

    if print_it or threshold_changed then
        print_histogram(histogram_no, dir_highlights, now)
    end

    return results
end


function M.pre_process(readings)
    local current_time = readings.now_s

    -- calculate which histogram to initialise
    local new_histogram_no = (floor(current_time / histogram_offset_seconds) % number_of_histograms) + 1

    if new_histogram_no ~= latest_histogram_no then
        if latest_histogram_no > 0 then -- first time through, there's nothing to print
            local prev_highlights = {}
            for idx, dir in ipairs(directions) do
                prev_highlights[idx] = dir.result_prev
            end
            print_histogram(new_histogram_no, prev_highlights, current_time)
        end
        -- every hour, the next histogram is re-initialised to 0
        latest_histogram_no = initialise_histogram(new_histogram_no, current_time)
    end

    -- Collect histogram data when network load is low
    for _, dir in ipairs(directions) do
        local is_low_load
        if use_relative_low_load then
            is_low_load = readings[dir.load_key] <= low_load_threshold
        else
            is_low_load = readings[dir.utilisation_key] <= dir.min_speed
        end

        if is_low_load then
            -- the bottom and top buckets are 'asymmetric', covering many more delays that are 'less' interesting
            local delay = limit(ceil(readings[dir.del_stat_key]), min_allowed_threshold, max_allowed_threshold)
            -- update all histograms, newest, oldest, and in-between
            for i = 1, number_of_histograms do
                local t = dir.histogram[i]
                t[delay] = t[delay] + 1
                dir.count[i] = dir.count[i] + 1
            end
        end
    end

    -- Periodically recalculate thresholds
    if (current_time - last_recalculated_time) >= recalculation_seconds then
        last_recalculated_time = current_time

        -- calculate oldest histogram (with the most readings)
        local oldest_histogram_no = latest_histogram_no + 1
        if oldest_histogram_no > number_of_histograms then
            oldest_histogram_no = 1
        end

        local results = calculate_thresholds(oldest_histogram_no, false, current_time)

        for _, dir in ipairs(directions) do
            dir.result_prev = results[dir.threshold_result_key]
        end

        return results
    end

    return {}
end


local function adjust_speed_reset(readings, histogram_no)
    local results = {}
    for _, dir in ipairs(directions) do
        if dir.good_count
            and readings[dir.next_rate_key] <= dir.min_speed
            and readings[dir.next_rate_key] < readings[dir.cur_rate_key] then
            local delay = limit(ceil(readings[dir.del_stat_key]), min_allowed_threshold, max_allowed_threshold)
            if delay > (dir.result_prev or dir.threshold_default) then
                local t = dir.histogram[histogram_no]
                local x = 0
                -- find the number of delays at this level and higher
                for i = delay, max_allowed_threshold do
                    x = x + t[i]
                end
                if x == 1 then
                    -- for the first delay, reduce the speed to half way between the current and the minimum
                    -- however ignore the change when close to the minimum is reached to avoid polluting the logs
                    local next_speed = floor(dir.min_speed + (readings[dir.cur_rate_key] - dir.min_speed) / 2)
                    if next_speed > dir.min_speed * 1.1 then
                        results[dir.next_rate_key] = next_speed
                    end
                end
            end
        end
    end

    return results
end


function M.process(readings)
    local results = {}

    -- detect a speed reset
    -- in main rate control loop, this happens when there is a high delay at a low load
    local speed_reset = false
    for _, dir in ipairs(directions) do
        if readings[dir.next_rate_key] <= dir.min_speed
            and readings[dir.next_rate_key] < readings[dir.cur_rate_key] then
            speed_reset = true
            break
        end
    end

    if speed_reset then
        -- calculate oldest histogram (with the most readings)
        local oldest_histogram_no = latest_histogram_no + 1
        if oldest_histogram_no > number_of_histograms then
            oldest_histogram_no = 1
        end

        -- Force a threshold recalculation on speed reset for freshest data
        local threshold_results = calculate_thresholds(oldest_histogram_no, true, readings.now_s)
        for _, dir in ipairs(directions) do
            dir.result_prev = threshold_results[dir.threshold_result_key]
        end

        -- check whether the histogram allows a speed reset to be mitigated
        results = adjust_speed_reset(readings, oldest_histogram_no)
    end

    return results
end

-- return the module
return M
