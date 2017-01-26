/*
Copyright (c) 2016 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Robert Y. Lewis
*/
#include "library/vm/vm_name.h"
#include "library/vm/vm_expr.h"
#include "library/tactic/tactic_state.h"
#include "library/app_builder.h"
#include "library/util.h"
#include "library/type_context.h"
#include "library/trace.h"
#include "library/constants.h"
#include "library/vm/vm_nat.h"
#include "library/vm/vm_string.h"
#include "library/norm_num.h"
#include <string>
#include "library/tactic/elaborate.h"
#include "library/wl_mathlink.h"
#include "library/tactic/mathematica_tactics.h"

namespace lean {
  
  vm_obj tactic_wl_execute_str(vm_obj const & e, vm_obj const & s) {
    expr e1 = wl_process_cmd(to_string(e));
    return mk_tactic_success(to_obj(e1), to_tactic_state(s));
  }

  void initialize_mathematica_tactic() {
    DECLARE_VM_BUILTIN(name({"tactic", "wl_execute_str"}), tactic_wl_execute_str);
  }

  void finalize_mathematica_tactic() {
  }

}
