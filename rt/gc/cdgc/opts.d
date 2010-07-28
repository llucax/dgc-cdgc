/**
 * This module contains the options managemente code of the garbage collector.
 *
 * Copyright: Copyright (C) 2010 Leandro Lucarella <http://www.llucax.com.ar/>
 *            All rights reserved.
 *
 * License: Boost Software License - Version 1.0 - August 17th, 2003
 *
 * Permission is hereby granted, free of charge, to any person or organization
 * obtaining a copy of the software and accompanying documentation covered by
 * this license (the "Software") to use, reproduce, display, distribute,
 * execute, and transmit the Software, and to prepare derivative works of the
 * Software, and to permit third-parties to whom the Software is furnished to
 * do so, all subject to the following:
 *
 * The copyright notices in the Software and this entire statement, including
 * the above license grant, this restriction and the following disclaimer,
 * must be included in all copies of the Software, in whole or in part, and
 * all derivative works of the Software, unless such copies or derivative
 * works are solely in the form of machine-executable object code generated by
 * a source language processor.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE, TITLE AND NON-INFRINGEMENT. IN NO EVENT
 * SHALL THE COPYRIGHT HOLDERS OR ANYONE DISTRIBUTING THE SOFTWARE BE LIABLE
 * FOR ANY DAMAGES OR OTHER LIABILITY, WHETHER IN CONTRACT, TORT OR OTHERWISE,
 * ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
 * DEALINGS IN THE SOFTWARE.
 *
 * Authors: Leandro Lucarella
 */

module rt.gc.cdgc.opts;

import cstdlib = tango.stdc.stdlib;
import cstring = tango.stdc.string;


private:


const MAX_OPT_LEN = 256;


struct Options
{
    uint verbose = 0;
    char[MAX_OPT_LEN] log_file = "";
    char[MAX_OPT_LEN] malloc_stats_file = "";
    char[MAX_OPT_LEN] collect_stats_file = "";
    bool sentinel = false;
    bool mem_stomp = false;
}

package Options options;


bool cstr_eq(char* s1, char* s2)
{
    return cstring.strcmp(s1, s2) == 0;
}


bool parse_bool(char* value)
{
    if (value[0] == '\0')
        return true;
    return (cstdlib.atoi(value) != 0);
}


void process_option(char* opt_name, char* opt_value)
{
    if (cstr_eq(opt_name, "verbose"))
        options.verbose = cstdlib.atoi(opt_value);
    else if (cstr_eq(opt_name, "log_file"))
        cstring.strcpy(options.log_file.ptr, opt_value);
    else if (cstr_eq(opt_name, "malloc_stats_file"))
        cstring.strcpy(options.malloc_stats_file.ptr, opt_value);
    else if (cstr_eq(opt_name, "collect_stats_file"))
        cstring.strcpy(options.collect_stats_file.ptr, opt_value);
    else if (cstr_eq(opt_name, "sentinel"))
        options.sentinel = parse_bool(opt_value);
    else if (cstr_eq(opt_name, "mem_stomp"))
        options.mem_stomp = parse_bool(opt_value);
}


package void parse(char* opts_string)
{
    char[MAX_OPT_LEN] opt_name;
    char[MAX_OPT_LEN] opt_value;
    char* curr = opt_name.ptr;
    size_t i = 0;
    if (opts_string is null)
        return;
    for (; *opts_string != '\0'; opts_string++)
    {
        char c = *opts_string;
        if (i == MAX_OPT_LEN)
        {
            if (c != ':')
                continue;
            else
                i--;
        }
        switch (*opts_string)
        {
        case ':':
            curr[i] = '\0';
            process_option(opt_name.ptr, opt_value.ptr);
            i = 0;
            opt_name[0] = '\0';
            opt_value[0] = '\0';
            curr = opt_name.ptr;
            break;
        case '=':
            opt_name[i] = '\0';
            curr = opt_value.ptr;
            i = 0;
            break;
        default:
            curr[i] = c;
            ++i;
        }
    }
    if (i == MAX_OPT_LEN)
        i--;
    curr[i] = '\0';
    process_option(opt_name.ptr, opt_value.ptr);
}


unittest
{
    with (options) {
        assert (verbose == 0);
        assert (log_file[0] == '\0');
        assert (sentinel == false);
        assert (mem_stomp == false);
    }
    parse("mem_stomp=1:verbose=2");
    with (options) {
        assert (verbose == 2);
        assert (log_file[0] == '\0');
        assert (sentinel == false);
        assert (mem_stomp == true);
    }
    parse("log_file=12345 67890:verbose=1:sentinel=4:mem_stomp=0");
    with (options) {
        assert (verbose == 1);
        assert (cstring.strcmp(log_file.ptr, "12345 67890".ptr) == 0);
        assert (sentinel == true);
        assert (mem_stomp == false);
    }
    parse(null);
    with (options) {
        assert (verbose == 1);
        assert (cstring.strcmp(log_file.ptr, "12345 67890".ptr) == 0);
        assert (sentinel == true);
        assert (mem_stomp == false);
    }
}


// vim: set et sw=4 sts=4 :
