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


  MLINK mlp;
  MLEnvironment mlpenv;
  
  static const char* fns_path = "~/lean/lean/extras/mathematica/ml_lean_form.m";

  void initiate_link() {
    int pid;
    char * args[5] = {"-linkname", "math -mathlink", "-linkmode", "launch",  NULL};
    MLEnvironment mlpe = MLInitialize(NULL);
    if (mlpe==NULL) {throw exception("mathlink failed at 2 : null env");}
    //std::cout << "made env\n";
    int open_error;
    MLINK ml = MLOpenInEnv(mlpe, 4, args, &open_error);
    if (ml==NULL) {throw exception("mathlink failed at 2 : null ml");}
    //std::cout << "made link\n";
    MLActivate(ml);
    //std::cout << "activated link\n";
    while (MLReady(ml)) {MLNextPacket(ml); MLNewPacket(ml);}
    //std::cout << "ready\n";
    MLPutFunction(ml, "EvaluatePacket", 1);
    MLPutSymbol(ml, "$ProcessID");
    MLEndPacket(ml);
    //std::cout << "ended packet\n";
    while (MLNextPacket(ml) != RETURNPKT) MLNewPacket(ml);
    //std::cout << "getting integer\n";
    MLGetInteger(ml, &pid);
    //std::cout << "got integer\n";
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
    //std::cout << "send wl command\n";
    if (mlp==nullptr) {
      //std::cout << "initiate link\n";
      initiate_link();
    }
    if (mlp == nullptr) {
      //std::cout << "still null??\n";
    }
    //std::cout << "put function\n";
    MLPutFunction(mlp, "EvaluatePacket", 1);
    MLPutFunction(mlp, "ToExpression", 1);
    //std::cout << "putting string: " << cmd.c_str() << "\n";
    MLPutString(mlp, cmd.c_str());
    MLEndPacket(mlp);
    //std::cout << "ended packet\n";
    //std::cout << MLNextPacket(mlp);
    while (MLNextPacket(mlp) != RETURNPKT) MLNewPacket(mlp);
    //std::cout << "finished send command\n";
  }


  /* typedef std::function<expr(expr *)> expr_fn;
  typedef std::pair<unsigned, expr_fn> expr_fn_ar;
  typedef std::unordered_map<string, expr> const_map;

  const expr mk_translate_constant(string hd) {
    if (hd == "nat") {
      return mk_constant(get_nat_name());
    } else if (hd == "rat") {
      return mk_constant(name("rat"));
    } else if (hd == "int") {
      return mk_constant(get_int_name());
    }  else if (hd == "real") {
      return mk_constant(name("real"));
    }else if (hd == "True") {
      return mk_constant(get_true_name());
    } else if (hd == "False") {
      return mk_constant(get_false_name());
    } else if (hd == "LeanPlaceholder") {
      return mk_expr_placeholder();
    } else {
      return mk_local(name(hd), mk_expr_placeholder());
    }
  }

  const expr_fn mk_translate_constructor(string hd, int nargs) {
    if (hd == "LeanAdd") {
      return [](expr * args) {
	return mk_app(mk_constant(get_add_name()), args[0], args[1]);
      };

    } else if (hd == "LeanMul") {
      return [](expr * args) {
	return mk_app(mk_constant(get_mul_name()), args[0], args[1]);
      };

    } else if (hd == "Subtract") {
      return [](expr * args) {
	return mk_app(mk_constant(get_sub_name()), args[0], args[1]);
      };

    } else if (hd == "Divide" || hd == "Rational") {
      return [](expr * args) {
	return mk_app(mk_constant(get_div_name()), args[0], args[1]);
      };

    } else if (hd == "Negative") {
      return [](expr * args) {
	return mk_app(mk_constant(get_neg_name()), args[0]);
      };

    } else if (hd == "Eq") {
      return [](expr * args) {
	return mk_app(mk_constant(get_eq_name()), args[0], args[1]);
      };

    } else if (hd == "Power") {
      return [](expr * args) {
	return mk_app(mk_constant(name("pow_nat")), args[0], args[1]);
      };

    } else if (hd == "And") {
      return [](expr * args) {
	return mk_app(mk_constant(get_and_name()), args[0], args[1]);
      };

    } else if (hd == "Or") {
      return [](expr * args) {
	return mk_app(mk_constant(get_or_name()), args[0], args[1]);
      };
      
    } else if (hd == "Implies") {
      return [](expr * args) {
	return mk_app(mk_constant(get_implies_name()), args[0], args[1]);
      };
      
    } else if (hd == "Not") {
      return [](expr * args) {
	return mk_app(mk_constant(get_not_name()), args[0]);
      };

    } else if (hd == "LeanForAll") {
      return [](expr * args) {
	expr body = abstract(args[2], args[0]);
	return mk_pi(mlocal_name(args[0]), args[1], body);
      };

    } else if (hd == "LeanExists") {
      return [](expr * args) {
	expr body = abstract(args[2], args[0]);
	expr lam = mk_lambda(mlocal_name(args[0]), args[1], body);
	return mk_app(mk_constant(get_Exists_name()), args[1], lam);
      };
      
    } else if (hd == "LeanApp") {
      return [](expr * args) {
	expr e0 = args[0];
	expr e1 = args[1];
	//std::cout << "making app: " << mk_app(e0, e1) << "\n";
	return mk_app(e0, e1); // mk_as_is?
      };

    } else if (hd == "ListCons") {
      return [](expr * args) {
	return mk_app(mk_constant(name("list", "cons")), args[0], args[1]);
      };

    } else if (hd == "ListEnd") {
      return [](expr * args) {
	return mk_app(mk_constant(name("list", "cons")), args[0], mk_constant(name("list", "nil")));
      };

    } else if (hd == "LeanAnd") {
      return [](expr * args) {
	return mk_app(mk_constant(get_and_name()), args[0], args[1]);
      };

    } else if (hd == "LeanOr") {
      return [](expr * args) {
	return mk_app(mk_constant(get_or_name()), args[0], args[1]);
      };

    } else if (hd == "Function") {
      return [](expr * args) {
	return Fun(args[0], args[1]);
      };
      
    } else if (hd == "LeanVar") {
      return [](expr * args) {
	name nm = mlocal_name(args[0]);
	return mk_local(nm, mk_expr_placeholder());
      };
    } else if (hd == "LeanLocal") {
      return [](expr * args) {
        return args[0];
      };
    } else if (hd == "LeanConst") {
      return [](expr * args) {
	return mk_partial_explicit(mk_constant(mlocal_name(args[0]), {mk_level_placeholder()}));
      };
    } else if (hd == "LeanPair") {
      return [](expr * args) {
	return mk_app(mk_constant(get_prod_mk_name()), args[0], args[1]);
      };
    } else if (hd == "LeanLevelParam") {
      return [](expr * args) {
	return args[0];
      };
    } else {
      return [&hd, &nargs](expr * args) {
	//std::cout << "making explicit hd: " << hd << "\n";
	expr ah = mk_partial_explicit(mk_constant(name(hd), {mk_level_placeholder()}));
	buffer<expr> newargs = buffer<expr>();
	newargs.push_back(ah);
	for (int i = 0; i < nargs; i++) {
	  newargs.push_back(args[i]);
	}
	return mk_app(newargs); // mk_as_is?
      };
    }
    }*/

  /*expr pnum_of_int(int n) {
    if (n < 0) return mk_app(mk_constant(name("signed_num", "neg_succ")), pnum_of_int(-(n+1)));
    if (n == 0) return mk_constant(name("signed_num", "zero"));
    if (n == 1) return mk_constant(get_one_name());
    if (n%2 == 0) return mk_app(mk_constant(get_bit0_name()), pnum_of_int(n/2));
    else return mk_app(mk_constant(get_bit1_name()), pnum_of_int(n/2));
  }*/

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
    //while (MLNextPacket(mlp) != RETURNPKT) MLNewPacket(mlp);
    auto tp = MLGetType(mlp);
    // std::cout << "tp: " << tp << "\n";
    switch (tp) {
    case MLTKSTR: { // Return a string wrapped in a local variable. This should be unpacked immediately
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
    // error
  }

  expr wl_process_cmd(string cmd) {
    //std::cout << "starting process_cmd\nProcessing: " << cmd << "\n\n";
    send_wl_command(cmd);
    //std::cout << "sent command!\n";
    expr e = expr_from_wl_link();
    //std::cout << "got expr: " << e << "\n";
    //reset_link(mlp);
    //std::cout << "reset link!\n";
    return e;
  }
  
}
