/*
Copyright (c) 2016 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis
*/
#include "library/wl_mathlink.h"
#include "library/constants.h"
#include "library/app_builder.h"
#include "library/explicit.h"
#include "library/placeholder.h"
#include "kernel/abstract.h"
#include "library/string.h"
#include <fstream>
#include <string>

using namespace std;

namespace lean {


  MLINK * mlpptr = nullptr;
  MLEnvironment * mlpenvptr = nullptr;
  MLINK mlp;
  MLEnvironment mlpenv;
  
  static const char* fns_path = "~/lean/lean/extras/mathematica/ml_lean_form.m";

  void initiate_link() {
    int pid;
    char * args[5] = {"-linkname", "math -mathlink", "-linkmode", "launch",  NULL};
    MLEnvironment mlpe = MLInitialize(NULL);
    if (mlpe==NULL) {throw exception("mathlink failed at 2 : null env");}
    int open_error;
    MLINK ml = MLOpenInEnv(mlpe, 4, args, &open_error);
    if (ml==NULL) {throw exception("mathlink failed at 2 : null ml");}
    MLActivate(ml);
    while (MLReady(ml)) {MLNextPacket(ml); MLNewPacket(ml);}
    MLPutFunction(ml, "EvaluatePacket", 1);
    MLPutSymbol(ml, "$ProcessID");
    MLEndPacket(ml);
    while (MLNextPacket(ml) != RETURNPKT) MLNewPacket(ml);
    MLGetInteger(ml, &pid);
    //printf("process id: %d\n", pid);

    MLPutFunction(ml, "Get", 1);
    MLPutString(ml, fns_path);
    MLEndPacket(ml);
    while (MLNextPacket(ml) != RETURNPKT) MLNewPacket(ml);
    MLNewPacket(ml);

    mlp = ml;
    mlpenv = mlpe;
  }

  void send_wl_command(string cmd) {
    if (!mlp) {
      initiate_link();
    }
    if (!mlp) {
      throw exception("failed to initiate link to Mathematica");
    }    
    MLPutFunction(mlp, "EvaluatePacket", 1);
    MLPutFunction(mlp, "ToExpression", 1);
    MLPutString(mlp, cmd.c_str());
    MLEndPacket(mlp);
    while (MLNextPacket(mlp) != RETURNPKT) MLNewPacket(mlp);
  }

  expr pos_num_of_int(int n) {
    if (n == 1)   return mk_constant(name("pos_num", "one"));
    if (n%2 == 0) return mk_app(mk_constant(name("pos_num", "bit0")), pos_num_of_int(n/2));
    else          return mk_app(mk_constant(name("pos_num", "bit1")), pos_num_of_int(n/2));
  }
  
  expr num_of_int(int n) {
    if (n == 0) return mk_constant(name("num", "zero"));
    else        return mk_app(mk_constant(name("num", "pos")), pos_num_of_int(n));
  }

  expr signed_num_of_int(int n) {
    if (n < 0) return mk_app(mk_constant(name("signed_num", "neg_succ")), num_of_int(-(n+1)));
    else       return mk_app(mk_constant(name("signed_num", "pos")), num_of_int(n));
  }
  
  expr lean_string_of_string(const char * s) {
    expr e = from_string(s);
    return mk_app(mk_constant(name("mmexpr", "str")), e);
  }

  expr lean_int_of_int(int s) {
    expr e = signed_num_of_int(s);
    return mk_app(mk_constant(name("mmexpr", "mint")), e);
  }

  expr lean_symbol_of_string(const char * s) {
    expr e = from_string(s);
    return mk_app(mk_constant(name("mmexpr", "sym")), e);
  }

  expr lean_list_of_expr_buffer(buffer<expr> b) {
    expr l = mk_app({mk_constant(get_list_nil_name(), {(mk_level_zero())}), mk_constant(name("mmexpr"))});
    for (int i = b.size()-1; i >= 0; i--)
      l = mk_app({mk_constant(get_list_cons_name(), {(mk_level_zero())}), mk_constant(name("mmexpr")), b[i], l});
    return l;
  }

  expr lean_app_of_expr_of_list(expr hd, expr args) {
    return mk_app(mk_constant(name("mmexpr", "app")), hd, args);
  }
  
  expr expr_from_wl_link() {
    auto tp = MLGetType(mlp);
    switch (tp) {
    case MLTKSTR: { 
      const char *s;
      MLGetString(mlp, &s); // need to release?
      return lean_string_of_string(s);
      break;
    }
    case MLTKINT: {
      int s;
      MLGetInteger(mlp, &s);
      return lean_int_of_int(s);
      break;
    }
    case MLTKFUNC: {
      int len;
      MLGetArgCount(mlp, &len);
      const char *hd;
      MLGetSymbol(mlp, &hd); // COULD THIS BE WRONG?
      buffer<expr> args = buffer<expr>();
      for (int i = 0; i < len; i++) {
	args.push_back(expr_from_wl_link());
      }
      return lean_app_of_expr_of_list(lean_symbol_of_string(hd), lean_list_of_expr_buffer(args));
      break;
    }
    case MLTKREAL: {
      double d;
      MLGetReal(mlp, &d);
      throw exception("cannot handle reals from mathematica");
      break;
    }
    case MLTKSYM: {
      const char *s;
      MLGetSymbol(mlp, &s);
      return lean_symbol_of_string(s);
      break;
    }
    default:
      throw exception("MathLink type not understood");
    }
    throw exception("MathLink type not understood");
  }

  expr wl_process_cmd(string cmd) {
    send_wl_command(cmd);
    expr e = expr_from_wl_link();
    MLNewPacket(mlp);
    return e;
  }
  
}
