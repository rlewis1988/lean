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
#include "library/num.h"
#include <fstream>
#include <string>
#include "wl_get_executable.h"

using namespace std;

namespace lean {

  string get_mm_extras_path() {
    return get_mm_directory();
  }

  MLINK * mlpptr = nullptr;
  MLEnvironment * mlpenvptr = nullptr;
  MLINK mlp;
  MLEnvironment mlpenv;
  int mm_run_cntr = 0;
  
  //static const char* fns_path = (get_mm_directory() + string("/ml_lean_form.m")).c_str();

  void initiate_link() {
    int pid;
    string cmd2 = get_mm_executable() + string(" -mathlink");
    char * cmd3 = (char*)cmd2.c_str();
    string path1 = get_mm_directory() + string("/ml_lean_form.m");
    char * fns_path = (char*)path1.c_str();
    char * args[5] = {"-linkname", cmd3, "-linkmode", "launch",  NULL};
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

  /*expr pos_num_of_int(int n) {
    if (n == 1)   return mk_constant(name("pos_num", "one"));
    if (n%2 == 0) return mk_app(mk_constant(name("pos_num", "bit0")), pos_num_of_int(n/2));
    else          return mk_app(mk_constant(name("pos_num", "bit1")), pos_num_of_int(n/2));
  }
  
  expr num_of_int(int n) {
    if (n == 0) return mk_constant(name("num", "zero"));
    else        return mk_app(mk_constant(name("num", "pos")), pos_num_of_int(n));
  }
  */
  expr to_int_expr(int n) {
    if (n < 0) return mk_app(mk_constant(name("int", "neg_succ_of_nat")), to_nat_expr(mpz(n+1)));
    else       return mk_app(mk_constant(name("int", "of_nat")), to_nat_expr(mpz(n)));
  }
  
  expr lean_string_of_string(const char * s) {
    expr e = from_string(s);
    return mk_app(mk_constant(name("mmexpr", "mstr")), e);
  }

  expr lean_int_of_int(int s) {
    expr e = to_int_expr(s); //signed_num_of_int(s);
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

  expr lean_float_of_ints(int sign, int mantisa, int exponent) {
    expr esign = to_nat_expr(mpz(sign));
    expr emant = to_nat_expr(mpz(mantisa));
    expr eexp  = to_nat_expr(mpz(exponent));
    return mk_app(mk_constant(name("float", "mk")), esign, emant, eexp);
  }

  expr lean_mreal_of_ints(int sign, int mantisa, int exponent) {
    return mk_app(mk_constant(name("mmexpr", "mreal")), lean_float_of_ints(sign, mantisa, exponent));
  }

  typedef union {
  float f;
  struct {
    unsigned int mantisa : 23;
    unsigned int exponent : 8;
    unsigned int sign : 1;
  } parts;
  } double_cast;
  
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
      double_cast d1;
      d1.f = d;
      printf("sign = %x\n",d1.parts.sign);
      printf("exponent = %x\n",d1.parts.exponent);
      printf("mantisa = %x\n",d1.parts.mantisa);
      return lean_mreal_of_ints(d1.parts.sign, d1.parts.mantisa, d1.parts.exponent);
      //throw exception("cannot handle reals from mathematica");
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
    string ctx_nm = "LeanLink" + std::to_string(mm_run_cntr);
    mm_run_cntr++;
    send_wl_command("Begin[\""+ctx_nm+"`\"];");
    MLNewPacket(mlp);
    send_wl_command(cmd);
    expr e = expr_from_wl_link();
    MLNewPacket(mlp);
    send_wl_command("End[];");
    MLNewPacket(mlp);
    return e;
  }


  expr wl_process_global_cmd(string cmd) {
    send_wl_command(cmd);
    expr e = expr_from_wl_link();
    MLNewPacket(mlp);
    return e;
  }  
  
}
