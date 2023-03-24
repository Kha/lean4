/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sebastian Ullrich
*/
#include <string>
#include <map>
#include "library/time_task.h"
#include "library/trace.h"

namespace lean {

static std::map<std::string, second_duration> * g_cum_times;
static mutex * g_cum_times_mutex;
LEAN_THREAD_PTR(xtimeit, g_current_timeit);

void report_profiling_time(std::string const & category, second_duration time) {
    lock_guard<mutex> _(*g_cum_times_mutex);
    (*g_cum_times)[category] += time;
}

void display_cumulative_profiling_times(std::ostream & out) {
    if (g_cum_times->empty())
        return;
    sstream ss;
    ss << "cumulative profiling times:\n";
    for (auto const & p : *g_cum_times)
        ss << "\t" << p.first << " " << display_profiling_time{p.second} << "\n";
    // output atomically, like IO.print
    out << ss.str();
}

void initialize_time_task() {
    g_cum_times_mutex = new mutex;
    g_cum_times = new std::map<std::string, second_duration>;
}

void finalize_time_task() {
    delete g_cum_times;
    delete g_cum_times_mutex;
}

time_task::time_task(std::string const & category, options const & opts, name decl) :
        m_category(category) {
    if (get_profiler(opts)) {
        m_parent_timeit = g_current_timeit;
        m_timeit = optional<xtimeit>(get_profiling_threshold(opts), [=](prof_clock::duration duration) mutable {
            sstream ss;
            ss << m_category;
            if (decl)
                ss << " of " << decl;
            ss << " took " << display_profiling_time{duration} << "\n";
            // output atomically, like IO.print
            tout() << ss.str();
        });
        g_current_timeit = &*m_timeit;
    }
}

time_task::~time_task() {
    if (m_timeit) {
        report_profiling_time(m_category, m_timeit->get_elapsed());
        if (m_parent_timeit)
            // report exclusive times
            m_parent_timeit->exclude_duration(m_timeit->get_elapsed_inclusive());
        g_current_timeit = m_parent_timeit;
    }
}

excluded_time_task::excluded_time_task() {
    if (g_current_timeit) {
        m_parent_timeit = g_current_timeit;
        m_timeit = optional<xtimeit>([](prof_clock::duration) {});
        g_current_timeit = &*m_timeit;
    }
}

excluded_time_task::~excluded_time_task() {
    if (m_timeit) {
        if (m_parent_timeit) {
            m_parent_timeit->ignore(*m_timeit);
        }
        g_current_timeit = m_parent_timeit;
    }
}

/* profileit {α : Type} (category : String) (opts : Options) (fn : Unit → α) (decl : Name) : α */
extern "C" LEAN_EXPORT obj_res lean_profileit(b_obj_arg category, b_obj_arg opts, obj_arg fn, obj_arg decl) {
    time_task t(string_to_std(category),
                TO_REF(options, opts),
                name(decl));
    return apply_1(fn, box(0));
}
}
