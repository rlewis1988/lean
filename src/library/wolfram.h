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

enum class tree_kind {Const, Add, Mul, App};
  
struct w_term_tree {
  std::string c_head;
  w_term_tree * w_head;
  buffer<w_term_tree> * args;
  type_context * m_tc;

  expr to_expr_aux(expr const & type);

  
  public:
  w_term_tree(std::string nsym, buffer<w_term_tree> * nargs) {
    c_head = nsym;
    args = nargs;
  }

  w_term_tree(w_term_tree * nsym, buffer<w_term_tree> * nargs) {
    w_head = nsym;
    args = nargs;
    c_head = "";
  }

  w_term_tree(std::string nsym) {
    c_head = nsym;
    args = nullptr;
  }

  bool is_const_head() {
    return c_head != "";
  }

  bool is_var_head() {
    return w_head;
  }

  bool is_const() {
    return args == nullptr;
  }

  std::string to_string_args() {
    //std::cout << "in to_string_args. " << is_const_head() << is_const() << c_head << "\n";
    //std::cout << "num of args: " << args->size() << " " << args << "\n";
    std::string s = "";
    //buffer<w_term_tree> w = args->operator[](0);
    //std::cout << "first arg: " << args->operator[](0).c_head << "\n";
    /*for (int i = 0; i < w.size(); i++) {
      s += w[i].to_string();
      s+= "\n";
      }*/
    for (int i = 0; i < args->size(); i++) {
      s += (args->operator[](i)).to_string();
      s += "\n";
    }
    return s;
  }

  std::string to_string() {
    // std::cout << "in to_string! " << is_const() << is_const_head() << "\n";
    //char s[10000];
    std::string head;
    std::string argstr;
    if (is_const_head()) {
      head = c_head;
    } else {
      head = w_head -> to_string();
    }
    if (is_const()) {
      argstr = "CONSTANT";
    } else {
      argstr = to_string_args();
    }
    //std::cout << head << "!!!\n";
    std::string s = "TREE. HEAD: \n{\n " + head + "\n}\nARGS:\n{\n " + argstr + "\n}\n";
    //    sprintf(s, "TREE. HEAD: \n{\n %s\n}\nARGS:\n{\n %s\n}\n",
    //	    head, argstr);
	    //(is_const_head() ? c_head : w_head -> to_string()), (is_const() ? "CONSTANT" : to_string_args()));
    //std::cout << "have string for " << head << "\n";
    return s; //trim(s);
  }

  expr to_expr(expr const & type, type_context tc) {
    m_tc = &tc;
    return to_expr_aux(type);
  }
  
};
  
w_term_tree wolfram_to_tree(std::string  & input);
//w_term_tree expr_to_tree(expr const & exp);  // do this in Lean?

expr fold(std::function<expr(type_context, expr, expr)> op,
	  buffer<w_term_tree> args, expr const & type, type_context m_tc);
 
}

 
