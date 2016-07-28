/*
Copyright (c) 2016 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis
*/
#pragma once
#include <string>
#include "kernel/environment.h"
#include "library/type_context.h"
#include "library/app_builder.h"

namespace lean {

// trim from start
static inline std::string &ltrim(std::string &s) {
    s.erase(s.begin(), std::find_if(s.begin(), s.end(),
            std::not1(std::ptr_fun<int, int>(std::isspace))));
    return s;
}

// trim from end
static inline std::string &rtrim(std::string &s) {
    s.erase(std::find_if(s.rbegin(), s.rend(),
            std::not1(std::ptr_fun<int, int>(std::isspace))).base(), s.end());
    return s;
}

// trim from both ends
static inline std::string &trim(std::string s) {
    return ltrim(rtrim(s));
}

 pair<buffer<expr>,int> get_next_app_arg_expr_buffer(int i, std::string const & nin, std::unordered_map<std::string, expr> const & const_map);
  
 expr wolfram_to_lean(type_context & tctx, std::string const & input, std::unordered_map<std::string, expr> const & const_map, expr default_type = expr(), bool has_default_type = false);

 typedef std::unordered_map<std::string, std::string> stringmap;
 typedef std::unordered_map<std::string, expr> stringexprmap;
 
 /*
  * Converts a Lean expression e into a Mathematica-like string.
  * optional fvn maps names of local variables (as strings) to new names (as strings)
  * 
  */
 pair<std::string, stringexprmap> lean_to_wolfram(expr const & e, bool const & rename);

 inline std::string lean_to_wolfram(expr const & e) {
   return lean_to_wolfram(e, false).first;
 }
}


