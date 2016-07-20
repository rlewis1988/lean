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

 enum class tree_kind {Const, Add, Mul, Sub, Div, Neg, App, ConstApp};
 
struct w_term_tree {
  std::string c_head;
  tree_kind m_kind;
  w_term_tree * w_head;
  buffer<w_term_tree> * args;
  type_context * m_tc;
  
  public:

  /*w_term_tree(w_term_tree const & w) {
    if (w.is_const() || w.is_const_app()) {c_head = w.get_c_head();}
    if (w.is_app()) {w_head = new w_term_tree(w.get_w_head());}
    m_kind = w.get_kind();
    buffer<w_term_tree> b = buffer<w_term_tree>();
    auto const & ob = w.get_args();
    for (int i = 0; i < ob.size(); i++) b.push_back(w_term_tree(ob[i]));
    args = &b;
    }*/

  w_term_tree(std::string nsym, buffer<w_term_tree> nargs) {
    c_head = nsym;
    args = &nargs;
    m_kind = tree_kind::ConstApp;
  }

  w_term_tree(tree_kind kind, buffer<w_term_tree> nargs) {
    if (kind == tree_kind::ConstApp || kind == tree_kind::Const || kind == tree_kind::App) {
      throw exception("bad args to w_term_tree");
    }
    m_kind = kind;
    args = &nargs;
  }

  w_term_tree(w_term_tree nsym, buffer<w_term_tree> nargs) {
    w_head = &nsym;
    args = &nargs;
    //c_head = "";
    m_kind = tree_kind::App;
  }

  w_term_tree(std::string nsym) {
    c_head = nsym;
    m_kind = tree_kind::Const;
    args = nullptr;
  }

  buffer<w_term_tree> const & get_args() {
    if (args) return *args;
    else return buffer<w_term_tree>();
  }

  unsigned int const & num_args() {
    if (args) return get_args().size();
    else return 0;
  }

  bool const & is_const_head() {
    return m_kind != tree_kind::App;
  }

  bool const & is_app() {
    return m_kind == tree_kind::App;
  }

  bool const & is_const() {
    return m_kind == tree_kind::Const;
  }

  bool const & is_add() {
    return m_kind == tree_kind::Add;
  }

  bool const & is_mul() {
    return m_kind == tree_kind::Mul;
  }

  bool const & is_sub() {
    return m_kind == tree_kind::Sub;
  }

  bool const & is_div() {
    return m_kind == tree_kind::Div;
  }

  bool const & is_neg() {
    return m_kind == tree_kind::Neg;
  }

  bool const & is_const_app() {
    return m_kind == tree_kind::ConstApp;
  }

  std::string const & get_c_head() {
    return c_head;
  }
  
  w_term_tree const & get_w_head() {
    if (w_head) return *w_head;
    throw exception("no w_head");
  }

  tree_kind const & get_kind() {
    return m_kind;
  }

  std::string const & to_string_head();

  std::string const & to_string_args() {
    std::cout << "in to_string_args. " << is_const_head() << is_const() << "\n";
    std::cout << " args: " << args->size() << "\n";
    //std::cout << "num of args: " << args->size() << " " << args << "\n";
    std::string s = "";
     //buffer<w_term_tree> w = args->operator[](0);
    //std::cout << "first arg: " << args->operator[](0).c_head << "\n";
    /*for (int i = 0; i < w.size(); i++) {
      s += w[i].to_string();
      s+= "\n";
      }*/
    auto s1 = (*args)[0];
    std::cout << "have 0";
    auto s2 = (*args)[1];
    std::cout << "have 1";
    for (int i = 0; i < args->size(); i++) {
      s += (*args)[i].to_string();//(args->operator[](i)).to_string();
      s += "\n";
    }
    return s;
  }

  std::string const & to_string() {
    std::cout << "in to_string! " << to_string_head() << is_const() << is_const_head() << "\n";
    //char s[10000];
    std::string head = to_string_head();
    std::cout << "have head: " << head << "\n";
    std::string argstr;
    std::cout << "is_const? " << is_const() << "\n";
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
    std::cout << "have string for " << head << "\n";
    return s; //trim(s);
  }

  /*  expr to_expr(expr const & type, type_context tc) {
    m_tc = &tc;
    return to_expr_aux(type);
    }*/
  
};

 w_term_tree mk_add_tree(buffer<w_term_tree> nargs);

 w_term_tree mk_mul_tree(buffer<w_term_tree> nargs);
  
 w_term_tree mk_sub_tree(buffer<w_term_tree> nargs);
  
 w_term_tree mk_div_tree(buffer<w_term_tree> nargs);
  
w_term_tree mk_neg_tree(buffer<w_term_tree> nargs);
  
//w_term_tree wolfram_to_tree(std::string  & input);
//w_term_tree expr_to_tree(expr const & exp);  // do this in Lean?

expr fold(std::function<expr(type_context, expr, expr)> op,
	  buffer<w_term_tree> * args, expr const & type, type_context m_tc);

 std::string wolfram_string_of_tree(w_term_tree arg);

 expr to_expr(w_term_tree arg, expr const & type, type_context tc);

 pair<buffer<expr>,int> get_next_app_arg_expr_buffer(int i, std::string const & nin, std::unordered_map<std::string, expr> const & const_map);
  
 expr wolfram_to_lean(type_context & tctx, std::string const & input, std::unordered_map<std::string, expr> const & const_map, expr default_type = expr(), bool has_default_type = false);
 
}


