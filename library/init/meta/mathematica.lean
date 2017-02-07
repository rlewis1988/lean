
/-
Copyright (c) 2017 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis
-/

import .tactic
open expr string level name binder_info

-- this is local to avoid conflicts with library_dev
meta def int_to_format (i : int) : format :=
int.rec_on i (λ k, to_fmt k) (λ k, "-(1+" ++ to_fmt k ++ ")")

meta def htfi : has_to_format int := ⟨int_to_format⟩
local attribute [instance] htfi

meta instance : has_to_format unsigned := ⟨λ i, fin.rec_on i (λ val is_lt, val)⟩

-- signed_num is the type of integer binary numerals
inductive signed_num : Type 
| pos : num → signed_num
| neg_succ : num → signed_num

def int_of_signed_num : signed_num → int
| (signed_num.pos k) := int.of_nat (nat.of_num k)
| (signed_num.neg_succ k) := int.neg_succ_of_nat (nat.of_num k)

-- this has the expected behavior only if i is under the max size of unsigned
def unsigned_of_signed_num (i : signed_num) : unsigned := 
signed_num.rec_on i (λ k, unsigned.of_nat (nat.of_num k)) (λ k, unsigned.of_nat (nat.of_num k))


-- let expressions get unfolded before translation
meta def expand_let : expr → expr
| (elet nm tp val bod) := expr.replace bod (λ e n, match e with |var n := some val | _ := none end)
| e := e

-- this isn't used and probably duplicates code in expr
meta def expand_let_rec : expr → expr
| (elet nm tp val bod) := expr.replace (expand_let_rec bod) (λ e n, match e with |var n := some val | _ := none end)
| (mvar nm tp) := mvar nm (expand_let_rec tp)
| (local_const nm ppnm bi tp) := local_const nm ppnm bi (expand_let_rec tp)
| (app f e) := app (expand_let_rec f) (expand_let_rec e)
| (lam nm bi tp bod) := lam nm bi (expand_let_rec tp) (expand_let_rec bod)
| (pi nm bi tp bod) := pi nm bi (expand_let_rec tp) (expand_let_rec bod)
| e := e


/-
  The following definitions are used to reflect Lean syntax into Mathematica. We reflect the types
   - name
   - level
   - list level
   - binder_info
   - expr
-/

meta def mathematica_form_of_name : name → string
| anonymous         := "LeanNameAnonymous"
| (mk_string s nm)  := "LeanNameMkString[\"" ++ s ++ "\", " ++ mathematica_form_of_name nm ++ "]"
| (mk_numeral i nm) := "LeanNameMkNum[" ++ to_string i ++ ", " ++ mathematica_form_of_name nm ++ "]"

meta def mathematica_form_of_lvl : level → string
| zero              := "LeanZeroLevel"
| (succ l)          := "LeanLevelSucc[" ++ mathematica_form_of_lvl l ++ "]"
| (level.max l1 l2) := "LeanLevelMax[" ++ mathematica_form_of_lvl l1 ++ ", " ++ mathematica_form_of_lvl l2 ++ "]"
| (imax l1 l2)      := "LeanLevelIMax[" ++ mathematica_form_of_lvl l1 ++ ", " ++ mathematica_form_of_lvl l2 ++ "]"
| (param nm)        := "LeanLevelParam[̈" ++ mathematica_form_of_name nm ++ "]"
| (global nm)       := "LeanLevelGlobal[" ++ mathematica_form_of_name nm ++ "]"
| (mvar nm)         := "LeanLevelMeta[" ++ mathematica_form_of_name nm ++ "]"

meta def mathematica_form_of_lvl_list : list level → string
| []       := "LeanLevelListNil"
| (h :: t) := "LeanLevelListCons[" ++ mathematica_form_of_lvl h ++ ", " ++ mathematica_form_of_lvl_list t ++ "]"

meta def mathematica_form_of_binder_info : binder_info → string
| binder_info.default := "BinderInfoDefault"
| implicit            := "BinderInfoImplicit"
| strict_implicit     := "BinderInfoStrictImplicit"
| inst_implicit       := "BinderInfoInstImplicit"
| other               := "BinderInfoOther"

-- let expressions get unfolded before translation.
-- translating macro expressions is not supported.
meta def mathematica_form_of_expr : expr → string
| (var i)                     := "LeanVar[" ++ (format.to_string (to_fmt i) options.mk) ++ "]"
| (sort lvl)                  := "LeanSort[" ++ mathematica_form_of_lvl lvl ++ "]"
| (const nm lvls)             := "LeanConst[" ++ mathematica_form_of_name nm ++ ", " ++ 
                                     mathematica_form_of_lvl_list lvls ++ "]"
| (mvar nm tp)                := "LeanMetaVar[" ++ mathematica_form_of_name nm ++ ", " ++
                                     mathematica_form_of_expr tp ++ "]"
| (local_const nm ppnm bi tp) := "LeanLocal[" ++ mathematica_form_of_name nm ++ ", " ++ 
                                     mathematica_form_of_name ppnm ++ ", " ++ mathematica_form_of_binder_info bi ++ 
                                     ", " ++ mathematica_form_of_expr tp ++ "]"
| (app f e)                   := "LeanApp[" ++ mathematica_form_of_expr f ++ ", " ++
                                     mathematica_form_of_expr e ++ "]"
| (lam nm bi tp bod)          := "LeanLambda[" ++ mathematica_form_of_name nm ++ ", " ++ 
                                     mathematica_form_of_binder_info bi ++ ", " ++ 
                                     mathematica_form_of_expr tp ++ ", " ++ mathematica_form_of_expr bod ++ "]"
| (pi nm bi tp bod)           := "LeanPi[" ++ mathematica_form_of_name nm ++ ", " ++ 
                                     mathematica_form_of_binder_info bi ++ ", " ++ mathematica_form_of_expr tp ++
                                     ", " ++ mathematica_form_of_expr bod ++ "]"
| (elet nm tp val bod)        := mathematica_form_of_expr (expand_let (elet nm tp val bod))
| (macro mdf n mfn)           := "LeanMacro"

/-
  The following definitions are used to make pexprs out of various types.
-/

def even : nat → Prop
| 0 := true
| 1 := false
| (n+2) := even n

instance : Π k, decidable (even k)
| 0 := decidable.is_true trivial
| 1 := decidable.is_false not_false
| (n + 2) := @dite (even n) (even.decidable _) _ (λ H, decidable.is_true H) (λ H, decidable.is_false H)

meta def pexpr_of_nat : nat → pexpr
| 0 := `(zero)
| 1 := `(one)
| (n + 2) := if even n then `(bit0 %%(pexpr_of_nat (n/2 + 1))) else `(bit1 %%(pexpr_of_nat ((n+1) / 2)))

meta def pexpr_of_pos_num : pos_num → pexpr
| pos_num.one := `(one)
| (pos_num.bit1 n) := `(bit1 %%(pexpr_of_pos_num n))
| (pos_num.bit0 n) := `(bit0 %%(pexpr_of_pos_num n))

meta def pexpr_of_num : num → pexpr
| num.zero := `(zero)
| (num.pos k) := pexpr_of_pos_num k


meta def pexpr_of_signed_num : signed_num → pexpr
| (signed_num.pos k) := pexpr_of_num k
| (signed_num.neg_succ k) := `(-(%%(pexpr_of_num (k+1))))

meta def pexpr_of_char : char → pexpr
| (fin.mk k l) := `((fin.mk %%(pexpr_of_nat k) dec_trivial : char))

meta def pexpr_of_string : string → pexpr
| [] := `(list.nil)
| (h :: t) := `(list.cons %%(pexpr_of_char h) %%(pexpr_of_string t))


/-
   The type mmexpr reflects Mathematica expression syntax.
   Until Lean's library supports ℚ and floating points, we assume we will not see
   real, rat, or comp from Mathematica.
-/

inductive mmexpr : Type
| sym  : string → mmexpr
| str  : string → mmexpr
| mint : signed_num → mmexpr 
| app  : mmexpr → list mmexpr → mmexpr
--| real : pexpr → mmexpr 
--| rat  : pexpr → pexpr → mmexpr
--| comp : pexpr → pexpr → mmexpr 



/-
  The atomic Mathematica tactic takes a string, executes it in Mathematica, and returns
  an mmexpr.
-/
namespace tactic
meta constant wl_execute_str : string → tactic expr
end tactic

open mmexpr tactic

meta def mmexpr_list_to_format (f : mmexpr → format) : list mmexpr → format
| [] := to_fmt ""
| [h] := f h
| (h :: t) := f h ++ ", " ++ mmexpr_list_to_format t

meta def mmexpr_to_format : mmexpr → format
| (sym s)     := to_fmt s
| (str s)     := to_fmt "\"" ++ to_fmt s ++ "\""
| (mint i)    := to_fmt (int_of_signed_num i)
| (app e1 ls) := mmexpr_to_format e1 ++ to_fmt "[" ++ mmexpr_list_to_format mmexpr_to_format ls ++ to_fmt "]"
--| (real i)    := to_fmt "" --i
--| (rat i j)   := to_fmt "" --"(" ++ to_fmt i ++ "/" ++ to_fmt j ++ to_fmt ")"
--| (comp i j)  := to_fmt "" --"(" ++ to_fmt i ++ " + i*" ++ to_fmt j ++ to_fmt ")"


meta instance : has_to_format mmexpr := ⟨mmexpr_to_format⟩

/-
  The following defs (from Leo) are useful for creating pexprs.
  Todo(?): refactor some of the instances below to use these.
-/
meta def mk_local_const (n : name) : pexpr :=
let t := pexpr.mk_placeholder in
pexpr.of_raw_expr (local_const n n binder_info.default (pexpr.to_raw_expr t))

meta def mk_constant (n : name) : pexpr :=
pexpr.of_raw_expr (const n [])

meta def mk_lambda (x : pexpr) (b : pexpr) : pexpr :=
pexpr.of_raw_expr (lambdas [pexpr.to_raw_expr x] (pexpr.to_raw_expr b))

meta def mk_app_core : pexpr → list pexpr → pexpr
| fn []      := fn
| fn (x::xs) := pexpr.of_raw_expr (app (pexpr.to_raw_expr (mk_app_core fn xs)) (pexpr.to_raw_expr x))

meta def mk_app (fn : pexpr) (args : list pexpr) : pexpr :=
mk_app_core fn args^.reverse

/-
  The following instances allow us to infer translations from mmexprs to meaningful Lean terms.
  Some Mathematica expressions, e.g. 
    LeanConst[LeanNameMkString["nat", LeanNameAnonymous], LeanLevelListNil]
  correspond to fully elaborated Lean expressions, e.g. nat.
  Others, e.g. LeanListNil or LeanPlus[x, y], correspond to unelaborated preexpressions
  (the latter under the assumption that x and y corespond to preexpressions). 
-/

-- Classes
meta class mmexpr_has_to_pexpr (m : mmexpr) :=
(to_pexpr : pexpr)

meta class mmexpr_has_to_expr (m : mmexpr) :=
(to_expr : expr)

meta class mmexpr_has_to_binder_info (m : mmexpr) :=
(to_binder_info : binder_info)

meta class mmexpr_has_to_level (m : mmexpr) :=
(to_level : level)

meta class mmexpr_has_to_level_list (m : mmexpr) :=
(to_level_list : list level)

meta class mmexpr_has_to_name (m : mmexpr) :=
(to_name : name)

meta class mmexpr_list_has_to_pexpr_list (l : list mmexpr) :=
(to_pexpr_list : list pexpr)

meta class mmexpr_has_to_abstractable (m : mmexpr) :=
(to_abstractable : pexpr)

-- Extractors
meta def pexpr_of_mmexpr (m : mmexpr) [mmexpr_has_to_pexpr m] : pexpr :=
mmexpr_has_to_pexpr.to_pexpr m

meta def expr_of_mmexpr (m : mmexpr) [mmexpr_has_to_expr m] : expr :=
mmexpr_has_to_expr.to_expr m

meta def binder_info_of_mmexpr (m : mmexpr) [mmexpr_has_to_binder_info m] : binder_info :=
mmexpr_has_to_binder_info.to_binder_info m

meta def level_of_mmexpr (m : mmexpr) [mmexpr_has_to_level m] : level :=
mmexpr_has_to_level.to_level m

meta def level_list_of_mmexpr (m : mmexpr) [mmexpr_has_to_level_list m] : list level :=
mmexpr_has_to_level_list.to_level_list m

meta def name_of_mmexpr (m : mmexpr) [mmexpr_has_to_name m] : name :=
mmexpr_has_to_name.to_name m

meta def pexpr_list_of_mmexpr_list (l : list mmexpr) [mmexpr_list_has_to_pexpr_list l] :=
mmexpr_list_has_to_pexpr_list.to_pexpr_list l

meta def abstractable_of_mmexpr (m : mmexpr) [mmexpr_has_to_abstractable m] :=
mmexpr_has_to_abstractable m

-- Translations to binder_info
meta instance mmexpr_binder_info_default : mmexpr_has_to_binder_info (sym "BinderInfoDefault") :=
⟨_, binder_info.default⟩
meta instance mmexpr_binder_info_implicit : mmexpr_has_to_binder_info (sym "BinderInfoImplicit") :=
⟨_, binder_info.implicit⟩
meta instance mmexpr_binder_info_strict : mmexpr_has_to_binder_info (sym "BinderInfoStrictImplicit") :=
⟨_, binder_info.strict_implicit⟩
meta instance mmexpr_binder_info_inst : mmexpr_has_to_binder_info (sym "BinderInfoInstImplicit") :=
⟨_, binder_info.inst_implicit⟩
meta instance mmexpr_binder_info_other : mmexpr_has_to_binder_info (sym "BinderInfoOther") :=
⟨_, binder_info.other⟩

-- Translations to level lists
meta instance mmexpr_level_list_nil : mmexpr_has_to_level_list (sym "LeanLevelListNil") :=
⟨_, []⟩

meta instance mmexpr_level_list_cons (h t : mmexpr) [mmexpr_has_to_level h] [mmexpr_has_to_level_list t] :
      mmexpr_has_to_level_list (app (sym "LeanLevelListCons") [h, t]) :=
⟨_, list.cons (level_of_mmexpr h) (level_list_of_mmexpr t)⟩

-- Translations to levels
meta instance mmexpr_level_zero : mmexpr_has_to_level (sym "LeanZeroLevel") :=
⟨_, level.zero⟩

meta instance mmexpr_level_succ (m : mmexpr) [mmexpr_has_to_level m] :
      mmexpr_has_to_level (app (sym "LeanLevelSucc") [m]) :=
⟨_, level.succ (level_of_mmexpr m)⟩

meta instance mmexpr_level_max (m1 m2 : mmexpr) [mmexpr_has_to_level m1] [mmexpr_has_to_level m2] :
      mmexpr_has_to_level (app (sym "LeanLevelMax") [m1, m2]) :=
⟨_, level.max (level_of_mmexpr m1) (level_of_mmexpr m2)⟩

meta instance mmexpr_level_imax (m1 m2 : mmexpr) [mmexpr_has_to_level m1] [mmexpr_has_to_level m2] :
      mmexpr_has_to_level (app (sym "LeanLevelIMax") [m1, m2]) :=
⟨_, level.imax (level_of_mmexpr m1) (level_of_mmexpr m2)⟩

meta instance mmexpr_level_param (s : string) : mmexpr_has_to_level (app (sym "LeanLevelParam") [str s]) :=
⟨_, level.param s⟩

meta instance mmexpr_level_global (s : string) : mmexpr_has_to_level (app (sym "LeanLevelGlobal") [str s]) :=
⟨_, level.global s⟩

meta instance mmexpr_level_mvar(s : string) : mmexpr_has_to_level (app (sym "LeanLevelMeta") [str s]) :=
⟨_, level.mvar s⟩

-- Translations to names
meta instance mmexpr_name_anonymous : mmexpr_has_to_name (sym "LeanNameAnonymous") :=
⟨_, anonymous⟩

meta instance mmexpr_name_mk_string (s : string) (m : mmexpr) [mmexpr_has_to_name m] :
     mmexpr_has_to_name (app (sym "LeanNameMkString") [str s, m]) :=
⟨_, mk_string s (name_of_mmexpr m)⟩

meta instance mmexpr_name_mk_num (i : num) (m : mmexpr) [mmexpr_has_to_name m] :
      mmexpr_has_to_name (app (sym "LeanNameMkNum") [mint (signed_num.pos i), m]) :=
⟨_, mk_numeral (unsigned.of_nat (nat.of_num i)) (name_of_mmexpr m)⟩

-- Translations to list pexpr
meta instance mmexpr_list_nil : mmexpr_list_has_to_pexpr_list [] := 
⟨_, []⟩

meta instance mmexpr_list_cons (h : mmexpr) (t : list mmexpr) [mmexpr_has_to_pexpr h] 
     [mmexpr_list_has_to_pexpr_list t] : mmexpr_list_has_to_pexpr_list (h :: t) :=
⟨_, pexpr_of_mmexpr h :: pexpr_list_of_mmexpr_list t⟩

-- Translations to expr
-- For the most part, these unreflect reflected Lean expressions.
meta instance mmexpr_has_to_expr_var (i : signed_num) : mmexpr_has_to_expr (app (sym "LeanVar") [mint i]) :=
⟨_, (var (unsigned_of_signed_num i))⟩

meta instance mmexpr_has_to_expr_sort (m : mmexpr) [mmexpr_has_to_level m] : 
     mmexpr_has_to_expr (app (sym "LeanSort") [m]) :=
⟨_, sort (level_of_mmexpr m)⟩

meta instance mmexpr_has_to_expr_const (nm lvls : mmexpr) [mmexpr_has_to_name nm] [mmexpr_has_to_level_list lvls] :
     mmexpr_has_to_expr (app (sym "LeanConst") [nm, lvls]) := 
⟨_, const (name_of_mmexpr nm) (level_list_of_mmexpr lvls)⟩

meta instance mmexpr_has_to_expr_mvar (nm m : mmexpr) [mmexpr_has_to_name nm] [mmexpr_has_to_expr m] :
      mmexpr_has_to_expr (app (sym "LeanMetaVar") [nm, m]) :=
⟨_, mvar (name_of_mmexpr nm) (expr_of_mmexpr m)⟩

meta instance mmexpr_has_to_expr_local (nm ppnm bi tp : mmexpr) [mmexpr_has_to_name nm] 
     [mmexpr_has_to_name ppnm] [mmexpr_has_to_binder_info bi] [mmexpr_has_to_expr tp] : 
     mmexpr_has_to_expr (app (sym "LeanLocal") [nm,ppnm, bi, tp]) :=
⟨_, (expr.local_const (name_of_mmexpr nm) (name_of_mmexpr ppnm) (binder_info_of_mmexpr bi) (expr_of_mmexpr tp)) ⟩

meta instance mmexpr_has_to_expr_app (f e : mmexpr) [mmexpr_has_to_expr f] [mmexpr_has_to_expr e] : 
     mmexpr_has_to_expr (app (sym "LeanApp") [f, e]) :=
⟨_, expr.app (expr_of_mmexpr f) (expr_of_mmexpr e)⟩

meta instance mmexpr_has_to_expr_lam (nm bi tp bd : mmexpr) [mmexpr_has_to_name nm] 
     [mmexpr_has_to_binder_info bi] [mmexpr_has_to_expr tp] [mmexpr_has_to_expr bd] : 
     mmexpr_has_to_expr (app (sym "LeanLambda") [nm, bi, tp, bd]) :=
⟨_, lam (name_of_mmexpr nm) (binder_info_of_mmexpr bi) (expr_of_mmexpr tp) (expr_of_mmexpr bd)⟩

meta instance mmexpr_has_to_expr_pi (nm bi tp bd : mmexpr) [mmexpr_has_to_name nm] 
     [mmexpr_has_to_binder_info bi] [mmexpr_has_to_expr tp] [mmexpr_has_to_expr bd] :
     mmexpr_has_to_expr (app (sym "LeanPi") [nm, bi, tp, bd]) :=
⟨_, pi (name_of_mmexpr nm) (binder_info_of_mmexpr bi) (expr_of_mmexpr tp) (expr_of_mmexpr bd)⟩

-- Translation to abstractable
-- This is used for function abstraction
@[priority 1]
meta instance mmexpr_has_to_pexpr_sym (s : string) : mmexpr_has_to_pexpr (sym s) :=
⟨_, mk_local_const s⟩

-- Translations to pexpr
-- For the most part, these are how we assign Lean semantics to Mathematica expressions.
meta instance mmexpr_has_to_pexpr_of_has_to_expr (m : mmexpr) [mmexpr_has_to_expr m] : mmexpr_has_to_pexpr m :=
⟨_, pexpr.of_expr (expr_of_mmexpr m)⟩


/-meta instance mmexpr_has_to_pexpr_leanadd (x y : mmexpr) [mmexpr_has_to_pexpr x] [mmexpr_has_to_pexpr y] : mmexpr_has_to_pexpr (app (sym "LeanAdd") [x, y]) :=
⟨_, `(%%(pexpr_of_mmexpr x) + %%(pexpr_of_mmexpr y))⟩

meta instance mmexpr_has_to_pexpr_leanmul (x y : mmexpr) [mmexpr_has_to_pexpr x] [mmexpr_has_to_pexpr y] : mmexpr_has_to_pexpr (app (sym "LeanMul") [x, y]) :=
⟨_, `(%%(pexpr_of_mmexpr x) * %%(pexpr_of_mmexpr y))⟩

meta instance mmexpr_has_to_pexpr_list_nil : mmexpr_has_to_pexpr (sym "LeanListNil") :=
⟨_, `(list.nil)⟩

meta instance mmexpr_has_to_pexpr_list_cons (h t : mmexpr) [mmexpr_has_to_pexpr h] [mmexpr_has_to_pexpr t] : mmexpr_has_to_pexpr (app (sym "LeanListCons") [h, t]) :=
⟨_, `(list.cons %%(pexpr_of_mmexpr h) %%(pexpr_of_mmexpr t))⟩-/

meta def pexpr_fold_op_aux (op : pexpr) : pexpr → list pexpr → pexpr
| e [] := e
| e (h::t) := pexpr_fold_op_aux `(%%op %%e %%h) t

meta def pexpr_fold_op (dflt op : pexpr) : list pexpr → pexpr
| [] := dflt
| [h] := h
| (h::t) := pexpr_fold_op_aux op h t

meta instance mmexpr_has_to_pexpr_plus (l : list mmexpr) [mmexpr_list_has_to_pexpr_list l] :
     mmexpr_has_to_pexpr (app (sym "Plus") l) :=
⟨_, pexpr_fold_op `(0) `(add) (pexpr_list_of_mmexpr_list l)⟩

meta instance mmexpr_has_to_pexpr_times (l : list mmexpr) [mmexpr_list_has_to_pexpr_list l] :
     mmexpr_has_to_pexpr (app (sym "Times") l) :=
⟨_, pexpr_fold_op `(1) `(mul) (pexpr_list_of_mmexpr_list l)⟩

meta instance mmexpr_has_to_pexpr_list (l : list mmexpr) [mmexpr_list_has_to_pexpr_list l] : 
     mmexpr_has_to_pexpr (app (sym "List") l) :=
⟨_, list.foldr (λ h t, `(%%h :: %%t)) `([]) (pexpr_list_of_mmexpr_list l)⟩

-- FILL IN FUNCTION TRANSLATION
@[reducible]
meta def abstract_mmexpr_symbol (s : string) (new_s : mmexpr) : mmexpr → mmexpr
| (app e l) := app (abstract_mmexpr_symbol e) (list.map abstract_mmexpr_symbol l)
| (sym t)   := if s = t then new_s else sym t
| (str t)   := str t
| (mint i)  := mint i

/-meta instance abstract_has_to_pexpr (s : string) (news : mmexpr) [mmexpr_has_to_pexpr news] : Π (m : mmexpr) [mmexpr_has_to_pexpr m], mmexpr_has_to_pexpr (abstract_mmexpr_symbol s news m)
| (app e l) h := by apply_instance
| (sym t) h := by apply_instance 
| (str t) h := by apply_instance
| (mint i) h := by apply_instance-/

@[reducible]
meta def mk_name_mmexpr (s : string) : mmexpr := app (sym "LeanNameMkString") [str s, sym "LeanNameAnonymous"]

@[reducible]
meta def mk_local_mmexpr (s : string) : mmexpr := app (sym "LeanLocal") [mk_name_mmexpr s, mk_name_mmexpr s, sym "BinderInfoDefault", app (sym "LeanSort") [sym "LeanZeroLevel"]]

meta instance mk_local_has_to_pexpr (s : string) : mmexpr_has_to_pexpr (mk_local_mmexpr s) := 
by apply_instance


meta instance mmexpr_has_to_pexpr_function (s : string) (m : mmexpr) [mmexpr_has_to_pexpr  m] : mmexpr_has_to_pexpr (app (sym "Function") [sym s, m]) :=
⟨_, mk_lambda (mk_local_const s) (pexpr_of_mmexpr m)⟩

--meta instance mmexpr_has_to_pexpr_function (s : string) (m : mmexpr) [mmexpr_has_to_pexpr m] : mmexpr_has_to_pexpr (app (sym "Function") [sym s, m]) :=
/-meta instance mmexpr_has_to_pexpr_function (s : string) (m : mmexpr) [mmexpr_has_to_pexpr (abstract_mmexpr_symbol s (mk_local_mmexpr s) m)] : mmexpr_has_to_pexpr (app (sym "Function") [sym s, m]) :=
⟨_, mk_lambda (mk_local_const s) (pexpr_of_mmexpr (abstract_mmexpr_symbol s (mk_local_mmexpr s) m))⟩-/

--meta instance mmexpr_has_to_pexpr_function (s : string) (m : mmexpr) [h : mmexpr_has_to_pexpr (abstract_mmexpr_symbol s (app (sym "LeanLocal") [str "MMVAR_s", str "MMVAR_s", (sym "BinderInfoDefault"), app (sym "LeanConst") [str "nat", sym "LeanLevelListNil"]]) m)] : mmexpr_has_to_pexpr (app (sym "Function") [sym s, m]) :=
--⟨_, `(λ MMVAR_s, %%(@pexpr_of_mmexpr _ h))⟩
--⟨_, expr.abstract_local (@expr_of_mmexpr _ h) s⟩
/-
meta example : abstract_mmexpr_symbol "x" (sym "y") (app (sym "Plus") [sym "x", sym "x"]) = app (sym "Plus") [sym "y", sym "y"] := begin

end
-
vm_eval abstract_mmexpr_symbol "x"  (app (sym "LeanLocal") [str "MMVAR_s", str "MMVAR_s", (sym "BinderInfoDefault"), app (sym "LeanConst") [str "nat", sym "LeanLevelListNil"]]) (app (sym "Plus") [sym "x", sym "x"])

example : true = true := by do
 ex ← wl_execute_str "Function[x, x+x]",
  ex' ← to_expr `(pexpr_of_mmexpr %%ex),
  --let ex' := expr_of_mmexpr exm in do
  trace ex',
  infer_type ex' >>= trace,
  ex'' ← eval_expr pexpr ex',
  ex''' ← to_expr `((%%ex'' : ℕ → ℕ)),
  trace ex''',
  reflexivity
-/

--@[reducible] meta def add_fn : mmexpr := app (sym "Function") [sym "x", app (sym "LeanAdd") [sym "x", sym "x"]]

--set_option trace.class_instances true
--eval pexpr_of_mmexpr  add_fn

/-meta example : (abstract_mmexpr_symbol "x" (mk_local_mmexpr "x") (app (sym "LeanAdd") [sym "x", sym "x"])) = app (sym "LeanAdd") [mk_local_mmexpr "x", mk_local_mmexpr "x"] := rfl

meta example : abstract_mmexpr_symbol "x" (mk_local_mmexpr "x") (sym "x") = mk_local_mmexpr "x" := rfl
meta example (k) : abstract_mmexpr_symbol "x" (mk_local_mmexpr "x") (mint k) = mint k := rfl
meta example : abstract_mmexpr_symbol "x" (mk_local_mmexpr "x") (app (sym "hi") []) = app (sym "hi") [] := rfl

-/

meta instance mmexpr_has_to_pexpr_int (i : signed_num) : mmexpr_has_to_pexpr (mint i) :=
⟨_, pexpr_of_signed_num i⟩

meta instance mmexpr_has_to_pexpr_string (s : string)  : mmexpr_has_to_pexpr (mmexpr.str s) :=
⟨_, pexpr_of_string s⟩


/-
  User-facing tactics for calling Mathematica that build on wl_execute_expr 
-/

namespace tactic

meta def run_mm_command_on_expr (cmd : string → string) (e : expr) : tactic pexpr := do
 rval ← wl_execute_str $ cmd $ mathematica_form_of_expr e,
 --trace "rval: ", trace rval,
  pexe ← to_expr `(pexpr_of_mmexpr %%rval),
 eval_expr pexpr pexe

meta def run_mm_command_on_expr_using (cmd : string → string) (e : expr) (path : string) : tactic pexpr := do
 rval ← wl_execute_str ("Get[\"" ++ path ++ "\"]; " ++ (cmd (mathematica_form_of_expr e))),
 --trace "rval: ", trace rval,
 pexe ← to_expr `(pexpr_of_mmexpr %%rval),
 eval_expr pexpr pexe

meta def run_mm_command_on_exprs_using (cmd : string → string → string) (e1 e2 : expr) (path : string) :
     tactic pexpr := 
do
 rval ← wl_execute_str ("Get[\"" ++ path ++ "\"]; " ++ 
          (cmd (mathematica_form_of_expr e1) (mathematica_form_of_expr e2))),
 --trace "rval: ", trace rval,
 pexe ← to_expr `(pexpr_of_mmexpr %%rval),
 eval_expr pexpr pexe

end tactic
exit

open tactic
set_option class.instance_max_depth 64
example (a b c : ℕ) : true = true := by do
e ← to_expr `([a, b, c]) >>= run_mm_command_on_expr (λ s, s++" // LeanForm // Activate"),
to_expr e >>= trace,
reflexivity

example : true = true := by do
e ← wl_execute_str "Function[a, a+a]",
pexe ← to_expr `(pexpr_of_mmexpr %%e),
pxr ← eval_expr pexpr pexe,
to_expr `((%%pxr : ℕ → ℕ)) >>= trace,
reflexivity
