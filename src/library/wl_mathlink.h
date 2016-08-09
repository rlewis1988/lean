/*
Copyright (c) 2016 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis
*/
#pragma once
#include "mathlink.h"
#include "library/type_context.h"
#include <string>

namespace lean {

  MLINK send_wl_command(type_context ctx, local_context lctx, std::string cmd);
  void reset_link(type_context ctx, local_context lctx, std::unordered_map<std::string, expr> cm, MLINK lp);
  expr wl_process_cmd(type_context ctx, local_context lctx, std::unordered_map<std::string, expr> cm, std::string cmd);
  
}
