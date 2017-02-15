
/-
Copyright (c) 2017 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis
-/

import .tactic .rb_map
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

meta def pexpr_mk_app (fn : pexpr) (args : list pexpr) : pexpr :=
mk_app_core fn args^.reverse

section translation
open rb_lmap
meta instance : has_ordering string := ⟨λ s1 s2, name.cmp s1 s2⟩

meta def sym_trans_pexpr_rule := string × pexpr
meta def sym_trans_expr_rule := string × expr
meta def app_trans_pexpr_keyed_rule := string × (list mmexpr → tactic pexpr)
meta def app_trans_expr_keyed_rule := string × (list mmexpr → tactic expr)
meta def app_trans_pexpr_unkeyed_rule := mmexpr → list mmexpr → tactic pexpr
meta def app_trans_expr_unkeyed_rule := mmexpr → list mmexpr → tactic expr

meta def trans_env := rb_map string expr

-- databases

meta def mk_sym_trans_pexpr_db (l : list name) : tactic (rb_lmap string pexpr) := do
 dcls ← monad.mapm
  (λ n, do c ← mk_const n,
   eval_expr sym_trans_pexpr_rule c) 
  l,
 return $ rb_lmap.of_list dcls

meta def mk_sym_trans_expr_db (l : list name) : tactic (rb_lmap string expr) := do
 dcls ← monad.mapm
  (λ n, do c ← mk_const n,
   eval_expr sym_trans_expr_rule c)
  l,
 return $ rb_lmap.of_list dcls

meta def mk_app_trans_pexpr_keyed_db (l : list name) : tactic (rb_lmap string (list mmexpr → tactic pexpr)) := do
 dcls ← monad.mapm
  (λ n, do c ← mk_const n,
   eval_expr app_trans_pexpr_keyed_rule c) 
  l,
 return $ rb_lmap.of_list dcls

meta def mk_app_trans_expr_keyed_db (l : list name) : tactic (rb_lmap string (list mmexpr → tactic expr)) := do
 dcls ← monad.mapm
  (λ n, do c ← mk_const n,
   eval_expr app_trans_expr_keyed_rule c)
  l,
 return $ rb_lmap.of_list dcls

meta def mk_app_trans_pexpr_unkeyed_db (l : list name) : tactic (list (mmexpr → list mmexpr → tactic pexpr)) :=
monad.mapm (λ n, do c ← mk_const n, eval_expr app_trans_pexpr_unkeyed_rule c) l

meta def mk_app_trans_expr_unkeyed_db (l : list name) : tactic (list (mmexpr → list mmexpr → tactic expr)) :=
monad.mapm (λ n, do c ← mk_const n, eval_expr app_trans_expr_unkeyed_rule c) l

meta def sym_to_pexpr_rule : caching_user_attribute (rb_lmap string pexpr) :=
⟨`sym_to_pexpr, "rule for translating a mmexpr.sym to a pexpr", mk_sym_trans_pexpr_db, []⟩ 

meta def sym_to_expr_rule : caching_user_attribute (rb_lmap string expr) :=
⟨`sym_to_expr, "rule for translating a mmexpr.sym to a expr", mk_sym_trans_expr_db, []⟩ 

meta def app_to_pexpr_keyed_rule : caching_user_attribute (rb_lmap string (list mmexpr → tactic pexpr)) :=
⟨`app_to_pexpr_keyed, "rule for translating a mmexpr.app to a pexpr", mk_app_trans_pexpr_keyed_db, []⟩ 

meta def app_to_expr_keyed_rule : caching_user_attribute (rb_lmap string (list mmexpr → tactic expr)) :=
⟨`app_to_expr_keyed, "rule for translating a mmexpr.app to a expr", mk_app_trans_expr_keyed_db, []⟩ 

meta def app_to_pexpr_unkeyed_rule : caching_user_attribute (list (mmexpr → list mmexpr → tactic pexpr)) :=
⟨`app_to_pexpr_unkeyed, "rule for translating a mmexpr.app to a pexpr", mk_app_trans_pexpr_unkeyed_db, []⟩ 

meta def app_to_expr_unkeyed_rule : caching_user_attribute (list (mmexpr → list mmexpr → tactic expr)) :=
⟨`app_to_expr_unkeyed, "rule for translating a mmexpr.app to a expr", mk_app_trans_expr_unkeyed_db, []⟩ 

run_command attribute.register `sym_to_pexpr_rule
run_command attribute.register `sym_to_expr_rule
run_command attribute.register `app_to_pexpr_keyed_rule
run_command attribute.register `app_to_expr_keyed_rule
run_command attribute.register `app_to_pexpr_unkeyed_rule
run_command attribute.register `app_to_expr_unkeyed_rule


meta def expr_of_mmexpr_app_keyed : mmexpr → list mmexpr → tactic expr
 | (sym hd) args := do 
 expr_db ← caching_user_attribute.get_cache app_to_expr_keyed_rule,
 tactic.first (list.map (λ f : list mmexpr → tactic expr, f args) (find expr_db hd)) -- why is type for f needed?
 | (str s) args := failed
 | (mint i) args := failed
 | (app i j) args := failed

meta def expr_of_mmexpr_app_unkeyed (hd : mmexpr) (args : list mmexpr) : tactic expr := do
 expr_db ← caching_user_attribute.get_cache app_to_expr_unkeyed_rule,
 tactic.first (list.map (λ f : mmexpr → list mmexpr → tactic expr, f hd args) expr_db)

meta def expr_of_mmexpr_app_decomp (expr_of_mmexpr : mmexpr → tactic expr)
         (hd : mmexpr) (args : list mmexpr) : tactic expr := do
 hs ← expr_of_mmexpr hd,
 args' ← monad.mapm expr_of_mmexpr args,
 return $ expr.mk_app hs args'

meta def expr_of_mmexpr_app (expr_of_mmexpr : mmexpr → tactic expr)
         (m : mmexpr) (l : list mmexpr) : tactic expr :=
 expr_of_mmexpr_app_keyed m l <|> 
 expr_of_mmexpr_app_unkeyed m l <|> 
 expr_of_mmexpr_app_decomp expr_of_mmexpr m l

meta def pexpr_of_mmexpr_app_keyed : mmexpr → list mmexpr → tactic pexpr
 | (sym hd) args := do
 expr_db ← caching_user_attribute.get_cache app_to_pexpr_keyed_rule,
 tactic.first (list.map (λ f : list mmexpr → tactic pexpr, f args) (find expr_db hd)) -- why is type for f needed?
 | (str s) args := failed
 | (mint i) args := failed
 | (app i j) args := failed

meta def pexpr_of_mmexpr_app_unkeyed (hd : mmexpr) (args : list mmexpr) : tactic pexpr := do
 expr_db ← caching_user_attribute.get_cache app_to_pexpr_unkeyed_rule,
 tactic.first (list.map (λ f : mmexpr → list mmexpr → tactic pexpr, f hd args) expr_db)

meta def pexpr_of_mmexpr_app_decomp (pexpr_of_mmexpr : mmexpr → tactic pexpr)
         (hd : mmexpr) (args : list mmexpr) : tactic pexpr := do
 hs ← pexpr_of_mmexpr hd,
 args' ← monad.mapm pexpr_of_mmexpr args,
 return $ pexpr_mk_app hs args'

meta def pexpr_of_mmexpr_app (pexpr_of_mmexpr : mmexpr → tactic pexpr)
         (m : mmexpr) (l : list mmexpr) : tactic pexpr :=
 pexpr_of_mmexpr_app_keyed  m l <|> 
 pexpr_of_mmexpr_app_unkeyed  m l <|> 
 pexpr_of_mmexpr_app_decomp pexpr_of_mmexpr m l

meta def expr_of_mmexpr : mmexpr → tactic expr
| (sym s) := do
  expr_db ← caching_user_attribute.get_cache sym_to_expr_rule,
  match find expr_db s with
  | (h :: t) := return h
  | [] := fail ("Couldn't find translation for sym \"" ++ s ++ "\"")
 end
| (str s) := string.to_expr s
| (mint i) := failed
| (app hd args) := expr_of_mmexpr_app expr_of_mmexpr hd args 

meta def pexpr_of_mmexpr_aux (pexpr_of_mmexpr : mmexpr → tactic pexpr) : mmexpr → tactic pexpr
| (sym s) := do
  expr_db ← caching_user_attribute.get_cache sym_to_pexpr_rule,
  match find expr_db s with
  | (h :: t) := return h
  | [] := fail ("Couldn't find translation for sym \"" ++ s ++ "\"")
 end
| (str s) := fail "unreachable, str case shouldn't reach pexpr_of_mmexpr_aux"
| (mint i) := return $ pexpr_of_signed_num i
| (app hd args) := pexpr_of_mmexpr_app pexpr_of_mmexpr hd args 

meta def pexpr_of_mmexpr : mmexpr → tactic pexpr := 
λ m, (do e ← expr_of_mmexpr m, return `(%%e)) <|> (pexpr_of_mmexpr_aux pexpr_of_mmexpr m)

end translation

section unreflect
-- The nested inductive pattern-matcher doesn't support placeholders yet.
-- Clean these up when this is fixed. (#1334)
meta def level_of_mmexpr : mmexpr → tactic level 
| (sym "LeanZeroLevel") := return $ level.zero
| (app (sym "LeanLevelSucc") [m]) := do m' ← level_of_mmexpr m, return $ level.succ m'
| (app (sym "LeanLevelMax") [m1, m2]) := do 
  m1' ← level_of_mmexpr m1, 
  m2' ← level_of_mmexpr m2, 
  return $ level.max m1' m2'
| (app (sym "LeanLevelIMax") [m1, m2]) := do 
  m1' ← level_of_mmexpr m1, 
  m2' ← level_of_mmexpr m2, 
  return $ level.imax m1' m2'
| (app (sym "LeanLevelParam") [str s]) := return $ level.param s
| (app (sym "LeanLevelMeta") [str s]) := return $ level.mvar s
| (app h t) := failed
| (sym s) := failed
| (str s) := failed
| (mint i) := failed

meta def level_list_of_mmexpr : mmexpr → tactic (list level) 
| (sym "LeanLevelListNil") := return []
| (app (sym "LeanLevelListCons") [h, t]) := do 
  h' ← level_of_mmexpr h, 
  t' ← level_list_of_mmexpr t,
  return $ h' :: t'
| (app h t) := failed
| (sym s) := failed
| (str s) := failed
| (mint i) := failed

meta def name_of_mmexpr : mmexpr → tactic name 
| (sym "LeanNameAnonymous") := return $ name.anonymous
| (app (sym "LeanNameMkString") [str s, m]) := do 
  n ← name_of_mmexpr m, return $ name.mk_string s n
| (app (sym "LeanNameMkNum") [mint i, m]) := do 
  n ← name_of_mmexpr m, return $ name.mk_numeral (unsigned_of_signed_num i) n
| (app h t) := failed
| (sym s) := failed
| (str s) := failed
| (mint i) := failed

meta def binder_info_of_mmexpr : mmexpr → tactic binder_info 
| (sym "BinderInfoDefault") := return $ binder_info.default 
| (sym "BinderInfoImplicit") := return $ binder_info.implicit 
| (sym "BinderInfoStrictImplicit") := return $ binder_info.strict_implicit
| (sym "BinderInfoInstImplicit") := return $ binder_info.inst_implicit
| (sym "BinderInfoOther") := return $ binder_info.other
| _ := failed
end unreflect

section transl_expr_instances

@[app_to_expr_keyed]
meta def mmexpr_var_to_expr : app_trans_expr_keyed_rule :=
⟨"LeanVar", 
λ args, match args with
| [mint i] := return $ var (unsigned_of_signed_num i)
| _        := failed
end⟩ 

@[app_to_expr_keyed]
meta def mmexpr_sort_to_expr : app_trans_expr_keyed_rule :=
⟨"LeanSort",
λ args, match args with
| [m] := do lvl ← level_of_mmexpr m, return $ sort lvl
| _   := failed
end⟩

@[app_to_expr_keyed]
meta def mmexpr_const_to_expr : app_trans_expr_keyed_rule :=
⟨"LeanConst",
λ args, match args with
| [nm, lvls] := do nm' ← name_of_mmexpr nm, lvls' ← level_list_of_mmexpr lvls, return $ const nm' lvls'
| _   := failed
end⟩

@[app_to_expr_keyed]
meta def mmexpr_mvar_to_expr : app_trans_expr_keyed_rule :=
⟨"LeanMetaVar",
λ args, match args with
| [nm, tp] := do nm' ← name_of_mmexpr nm, tp' ← expr_of_mmexpr tp, return $ mvar nm' tp'
| _   := failed
end⟩

@[app_to_expr_keyed]
meta def mmexpr_local_to_expr : app_trans_expr_keyed_rule :=
⟨"LeanLocal",
λ args, match args with
| [nm, ppnm, bi, tp] := do 
  nm' ← name_of_mmexpr nm, 
  ppnm' ← name_of_mmexpr ppnm, 
  bi' ← binder_info_of_mmexpr bi, 
  tp' ← expr_of_mmexpr tp, 
  return $ expr.local_const nm' ppnm' bi' tp'
| _   := failed
end⟩

@[app_to_expr_keyed]
meta def mmexpr_app_to_expr : app_trans_expr_keyed_rule :=
⟨"LeanApp",
λ args, match args with
| [hd, bd] := do hd' ← expr_of_mmexpr hd, bd' ← expr_of_mmexpr bd, return $ expr.app hd' bd'
| _   := failed
end⟩

@[app_to_expr_keyed]
meta def mmexpr_lam_to_expr : app_trans_expr_keyed_rule :=
⟨"LeanLambda",
λ args, match args with
| [nm, bi, tp, bd] := do 
  nm' ← name_of_mmexpr nm, 
  bi' ← binder_info_of_mmexpr bi, 
  tp' ← expr_of_mmexpr tp,
  bd' ← expr_of_mmexpr bd,
  return $ lam nm' bi' tp' bd'
| _   := failed
end⟩

@[app_to_expr_keyed]
meta def mmexpr_pi_to_expr : app_trans_expr_keyed_rule :=
⟨"LeanPi",
λ args, match args with
| [nm, bi, tp, bd] := do 
  nm' ← name_of_mmexpr nm, 
  bi' ← binder_info_of_mmexpr bi, 
  tp' ← expr_of_mmexpr tp,
  bd' ← expr_of_mmexpr bd,
  return $ lam nm' bi' tp' bd'
| _ := failed
end⟩

meta def pexpr_fold_op_aux (op : pexpr) : pexpr → list pexpr → pexpr
| e [] := e
| e (h::t) := pexpr_fold_op_aux `(%%op %%e %%h) t

meta def pexpr_fold_op (dflt op : pexpr) : list pexpr → pexpr
| [] := dflt
| [h] := h
| (h::t) := pexpr_fold_op_aux op h t

-- pexpr instances

@[app_to_pexpr_keyed]
meta def add_to_pexpr : app_trans_pexpr_keyed_rule :=
⟨"Plus", 
λ args, do args' ← monad.for args pexpr_of_mmexpr, return $ pexpr_fold_op `(0) `(add) args'⟩

@[app_to_pexpr_keyed]
meta def mul_to_pexpr : app_trans_pexpr_keyed_rule :=
⟨"Times", 
λ args, do args' ← monad.for args pexpr_of_mmexpr, return $ pexpr_fold_op `(0) `(mul) args'⟩

@[app_to_pexpr_keyed]
meta def list_to_pexpr : app_trans_pexpr_keyed_rule := 
⟨"List",
λ args, do args' ← monad.for args pexpr_of_mmexpr, return $ list.foldr (λ h t, `(%%h :: %%t)) `([]) args'⟩

end transl_expr_instances

-- user-facing tactics
namespace tactic

meta def run_mm_command_on_expr (cmd : string → string) (e : expr) : tactic pexpr := do
 rval ← wl_execute_str $ cmd $ mathematica_form_of_expr e,
 rval' ← eval_expr mmexpr rval,
 pexpr_of_mmexpr rval'

meta def run_mm_command_on_expr_using (cmd : string → string) (e : expr) (path : string) : tactic pexpr := do
 rval ← wl_execute_str ("Get[\"" ++ path ++ "\"]; " ++ (cmd (mathematica_form_of_expr e))),
 --trace "rval: ", trace rval,
 rval' ← eval_expr mmexpr rval,
 pexpr_of_mmexpr rval'

meta def run_mm_command_on_exprs_using (cmd : string → string → string) (e1 e2 : expr) (path : string) :
     tactic pexpr := 
do
 rval ← wl_execute_str ("Get[\"" ++ path ++ "\"]; " ++ 
          (cmd (mathematica_form_of_expr e1) (mathematica_form_of_expr e2))),
 rval' ← eval_expr mmexpr rval,
 pexpr_of_mmexpr rval'

end tactic
