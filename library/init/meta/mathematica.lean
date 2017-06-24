/-
Copyright (c) 2017 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis
-/

import .tactic .rb_map
open expr string level name binder_info

meta instance : has_ordering string := ⟨λ s1 s2, name.cmp s1 s2⟩

meta def htfi : has_to_format ℤ := ⟨λ z, int.rec_on z (λ k, ↑k) (λ k, "-"++↑(k+1))⟩
local attribute [instance] htfi

structure float :=
(sign     : nat)
(mantisa  : nat)
(exponent : nat)

meta instance : has_to_format float :=
⟨λ f, to_fmt "(" ++ to_fmt f.sign ++ to_fmt ", " ++ 
      to_fmt f.mantisa ++ ", " ++ to_fmt f.exponent ++ to_fmt ")"⟩

meta instance : has_reflect float | ⟨s, m, e⟩ :=
((`(λ s' m' e', float.mk s' m' e').subst (nat.reflect s)).subst (nat.reflect m)).subst (nat.reflect e)

--`({float. sign := %%(reflect s), mantisa := %%(reflect m), exponent := %%(reflect e)})
--`(float.mk %%(nat.reflect s) %%(nat.reflect m) %%(nat.reflect e))
--⟨λ fl, `(float.mk %%(quote fl.sign) %%(quote fl.mantisa) %%(quote fl.exponent))⟩

-- signed_num is the type of integer binary numerals
/-inductive signed_num : Type 
| pos : num → signed_num
| neg_succ : num → signed_num

def int_of_signed_num : signed_num → int
| (signed_num.pos k) := int.of_nat k
| (signed_num.neg_succ k) := int.neg_succ_of_nat (nat.of_num k)

-- this has the expected behavior only if i is under the max size of unsigned
def unsigned_of_signed_num (i : int) : unsigned := 
int.rec_on i (λ k, unsigned.of_nat (nat.of_num k)) (λ k, unsigned.of_nat (nat.of_num k))

def nat_of_signed_num (i : signed_num) : nat := 
signed_num.rec_on i (λ k, nat.of_num k) (λ k, nat.of_num k)
-/



-- this has the expected behavior only if i is under the max size of unsigned
def unsigned_of_int (i : int) : unsigned := 
int.rec_on i (λ k, unsigned.of_nat k) (λ k, unsigned.of_nat k)


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
namespace mathematica
meta def form_of_name : name → string
| anonymous         := "LeanNameAnonymous"
| (mk_string s nm)  := "LeanNameMkString[\"" ++ s ++ "\", " ++ form_of_name nm ++ "]"
| (mk_numeral i nm) := "LeanNameMkNum[" ++ to_string i ++ ", " ++ form_of_name nm ++ "]"

meta def form_of_lvl : level → string
| zero              := "LeanZeroLevel"
| (succ l)          := "LeanLevelSucc[" ++ form_of_lvl l ++ "]"
| (level.max l1 l2) := "LeanLevelMax[" ++ form_of_lvl l1 ++ ", " ++ form_of_lvl l2 ++ "]"
| (imax l1 l2)      := "LeanLevelIMax[" ++ form_of_lvl l1 ++ ", " ++ form_of_lvl l2 ++ "]"
| (param nm)        := "LeanLevelParam[̈" ++ form_of_name nm ++ "]"
| (mvar nm)         := "LeanLevelMeta[" ++ form_of_name nm ++ "]"

meta def form_of_lvl_list : list level → string
| []       := "LeanLevelListNil"
| (h :: t) := "LeanLevelListCons[" ++ form_of_lvl h ++ ", " ++ form_of_lvl_list t ++ "]"

meta def form_of_binder_info : binder_info → string
| binder_info.default := "BinderInfoDefault"
| implicit            := "BinderInfoImplicit"
| strict_implicit     := "BinderInfoStrictImplicit"
| inst_implicit       := "BinderInfoInstImplicit"
| other               := "BinderInfoOther"

/-
  let expressions get unfolded before translation.
  translating macro expressions is not supported.
-/
meta def form_of_expr : expr → string
| (var i)                     := "LeanVar[" ++ (format.to_string (to_fmt i) options.mk) ++ "]"
| (sort lvl)                  := "LeanSort[" ++ form_of_lvl lvl ++ "]"
| (const nm lvls)             := "LeanConst[" ++ form_of_name nm ++ ", " ++ form_of_lvl_list lvls ++ "]"
| (mvar nm tp)                := "LeanMetaVar[" ++ form_of_name nm ++ ", " ++ form_of_expr tp ++ "]"
| (local_const nm ppnm bi tp) := "LeanLocal[" ++ form_of_name nm ++ ", " ++ 
                                     form_of_name ppnm ++ ", " ++ form_of_binder_info bi ++ 
                                     ", " ++ form_of_expr tp ++ "]"
| (app f e)                   := "LeanApp[" ++ form_of_expr f ++ ", " ++ form_of_expr e ++ "]"
| (lam nm bi tp bod)          := "LeanLambda[" ++ form_of_name nm ++ ", " ++ 
                                     form_of_binder_info bi ++ ", " ++ 
                                     form_of_expr tp ++ ", " ++ form_of_expr bod ++ "]"
| (pi nm bi tp bod)           := "LeanPi[" ++ form_of_name nm ++ ", " ++ 
                                     form_of_binder_info bi ++ ", " ++ form_of_expr tp ++
                                     ", " ++ form_of_expr bod ++ "]"
| (elet nm tp val bod)        := form_of_expr $ expand_let $ elet nm tp val bod
| (macro mdf mlst)           := "LeanMacro"

/-
These functions are difficult to implement without a monad map over expr. 
The problem: macros can be definitionally equal but have different meanings.
So we need to replace them in an expr as soon as we encounter them, which involves
generating a fresh name.

section
open tactic

meta def is_macro : expr → bool
| (macro _ _ _) := tt
| _             := ff

meta def find_macros (e : expr) : rb_set expr :=
e^.fold (rb_map.mk _ _) (λ ex _ map, if is_macro ex then map^.insert ex else map)

meta def {u} flip_pair_list {α : Type u} (l : list (α × α)) : list (α × α) :=
l^.map (λ ⟨p1, p2⟩, ⟨p2, p1⟩)

meta def remove_macros (e : expr) : tactic (expr × rb_map expr expr) :=
do ls ← (find_macros e)^.mfold [] (λ ex l, do mv ← infer_type ex >>= mk_meta_var, return ((ex, mv)::l)),
   replmap ← return $ rb_map.of_list ls,
   e' ← return $ e^.replace (λ ex _, replmap^.find ex),
   return (e', rb_map.of_list $ flip_pair_list ls)

meta def reinsert_macros (e : expr) (map : rb_map expr expr) : expr :=
e^.replace (λ ex _, map^.find ex)

--meta def reinsert_macros_in_mmexpr (m : mmexpr) (map : rb_map expr expr) : expr := sorry
-/

/-
  The following definitions are used to make pexprs out of various types.
-/
end mathematica

/-meta def pexpr_of_int : int → pexpr
| pos_num.one := `(one)
| (pos_num.bit1 n) := `(bit1 %%(pexpr_of_pos_num n))
| (pos_num.bit0 n) := `(bit0 %%(pexpr_of_pos_num n))

meta def pexpr_of_num : num → pexpr
| num.zero := `(zero)
| (num.pos k) := pexpr_of_pos_num k


meta def pexpr_of_signed_num : signed_num → pexpr
| (signed_num.pos k) := pexpr_of_num k
| (signed_num.neg_succ k) := `(-(%%(pexpr_of_num (k+1))))-/

meta def pexpr_of_nat : ℕ → pexpr
| 0 := ```(0)
| 1 := ```(1)
| k := if k%2=0 then ```(bit0 %%(pexpr_of_nat (k/2))) else ```(bit1 %%(pexpr_of_nat (k/2)))

meta def pexpr_of_int : int → pexpr
| (int.of_nat n) := pexpr_of_nat n
| (int.neg_succ_of_nat n) := ```(-%%(pexpr_of_nat (n+1)))

/--
The type mmexpr reflects Mathematica expression syntax.
-/
inductive mmexpr : Type
| sym   : string → mmexpr
| mstr  : string → mmexpr
| mint  : int → mmexpr 
| app   : mmexpr → list mmexpr → mmexpr
| mreal : float → mmexpr 

namespace tactic
namespace mathematica
/--
execute str evaluates str in Mathematica.
The evaluation happens in a unique context; declarations that are made during
evaluation will not be available in future evaluations.
-/
meta constant execute : string → tactic expr

/--
execute_global str evaluates str in Mathematica.
The evaluation happens in the global context; declarations that are made during
evaluation will persist.
-/
meta constant execute_global : string → tactic expr

/--
Returns the path to {LEAN_ROOT}/extras/mathematica
-/
meta constant extras_path : string --:= "~/lean/lean/extras/mathematica"
end mathematica
end tactic

namespace mathematica
open mmexpr tactic

meta def mmexpr_list_to_format (f : mmexpr → format) : list mmexpr → format
| []       := to_fmt ""
| [h]      := f h
| (h :: t) := f h ++ ", " ++ mmexpr_list_to_format t

meta def mmexpr_to_format : mmexpr → format
| (sym s)     := to_fmt s
| (mstr s)     := to_fmt "\"" ++ to_fmt s ++ "\""
| (mint i)    := to_fmt i
| (app e1 ls) := mmexpr_to_format e1 ++ to_fmt "[" ++ mmexpr_list_to_format mmexpr_to_format ls ++ to_fmt "]"
| (mreal r)   := to_fmt r 


meta instance : has_to_format mmexpr := ⟨mmexpr_to_format⟩

/-
  The following are useful for creating pexprs.
-/
/-private meta def mk_local_const (n : name) : pexpr :=
let t := pexpr.mk_placeholder in
(local_const n n binder_info.default t)

private meta def mk_constant (n : name) : pexpr :=
pexpr.of_raw_expr (const n [])

private meta def mk_lambda (x : pexpr) (b : pexpr) : pexpr :=
pexpr.of_raw_expr (lambdas [pexpr.to_raw_expr x] (pexpr.to_raw_expr b))

private meta def mk_app_core : pexpr → list pexpr → pexpr
| fn []      := fn
| fn (x::xs) := pexpr.of_raw_expr (app (pexpr.to_raw_expr (mk_app_core fn xs)) (pexpr.to_raw_expr x))

private meta def pexpr_mk_app (fn : pexpr) (args : list pexpr) : pexpr :=
mk_app_core fn args^.reverse-/

private meta def pexpr_mk_app : pexpr → list pexpr → pexpr
| fn [] := fn
| fn (h::t) := pexpr_mk_app (app fn h) t

section translation
open rb_lmap


@[reducible] meta def trans_env := rb_map string expr
meta def trans_env.empty := rb_map.mk string expr

meta def sym_trans_pexpr_rule := string × pexpr
meta def sym_trans_expr_rule := string × expr
meta def app_trans_pexpr_keyed_rule := string × (trans_env → list mmexpr → tactic pexpr)
meta def app_trans_expr_keyed_rule := string × (trans_env → list mmexpr → tactic expr)
meta def app_trans_pexpr_unkeyed_rule := trans_env → mmexpr → list mmexpr → tactic pexpr
meta def app_trans_expr_unkeyed_rule := trans_env → mmexpr → list mmexpr → tactic expr

-- databases

private meta def mk_sym_trans_pexpr_db (l : list name) : tactic (rb_lmap string pexpr) := 
do dcls ← monad.mapm (λ n, mk_const n >>= eval_expr sym_trans_pexpr_rule) l,
   return $ of_list dcls

private meta def mk_sym_trans_expr_db (l : list name) : tactic (rb_lmap string expr) := 
do dcls ← monad.mapm (λ n, mk_const n >>= eval_expr sym_trans_expr_rule) l,
   return $ of_list dcls

private meta def mk_app_trans_pexpr_keyed_db (l : list name) : 
     tactic (rb_lmap string (trans_env → list mmexpr → tactic pexpr)) := 
do dcls ← monad.mapm (λ n, mk_const n >>= eval_expr app_trans_pexpr_keyed_rule) l,
   return $ of_list dcls

private meta def mk_app_trans_expr_keyed_db (l : list name) : 
     tactic (rb_lmap string (trans_env → list mmexpr → tactic expr)) := 
do dcls ← monad.mapm (λ n, mk_const n >>= eval_expr app_trans_expr_keyed_rule) l,
   return $ of_list dcls

private meta def mk_app_trans_pexpr_unkeyed_db (l : list name) : 
     tactic (list (trans_env → mmexpr → list mmexpr → tactic pexpr)) :=
monad.mapm (λ n, mk_const n >>= eval_expr app_trans_pexpr_unkeyed_rule) l

private meta def mk_app_trans_expr_unkeyed_db (l : list name) : 
     tactic (list (trans_env → mmexpr → list mmexpr → tactic expr)) :=
monad.mapm (λ n, mk_const n >>= eval_expr app_trans_expr_unkeyed_rule) l

private meta def sym_to_pexpr_rule : caching_user_attribute (rb_lmap string pexpr) :=
⟨⟨`sym_to_pexpr, "rule for translating a mmexpr.sym to a pexpr"⟩, mk_sym_trans_pexpr_db, []⟩ 

private meta def sym_to_expr_rule : caching_user_attribute (rb_lmap string expr) :=
⟨⟨`sym_to_expr, "rule for translating a mmexpr.sym to a expr"⟩, mk_sym_trans_expr_db, []⟩ 

private meta def app_to_pexpr_keyed_rule : 
caching_user_attribute (rb_lmap string (trans_env → list mmexpr → tactic pexpr)) :=
⟨⟨`app_to_pexpr_keyed, "rule for translating a mmexpr.app to a pexpr"⟩, mk_app_trans_pexpr_keyed_db, []⟩ 

private meta def app_to_expr_keyed_rule : 
caching_user_attribute (rb_lmap string (trans_env → list mmexpr → tactic expr)) :=
⟨⟨`app_to_expr_keyed, "rule for translating a mmexpr.app to a expr"⟩, mk_app_trans_expr_keyed_db, []⟩ 

private meta def app_to_pexpr_unkeyed_rule : 
caching_user_attribute (list (trans_env → mmexpr → list mmexpr → tactic pexpr)) :=
⟨⟨`app_to_pexpr_unkeyed, "rule for translating a mmexpr.app to a pexpr"⟩, mk_app_trans_pexpr_unkeyed_db, []⟩ 

private meta def app_to_expr_unkeyed_rule : 
caching_user_attribute (list (trans_env → mmexpr → list mmexpr → tactic expr)) :=
⟨⟨`app_to_expr_unkeyed, "rule for translating a mmexpr.app to a expr"⟩, mk_app_trans_expr_unkeyed_db, []⟩ 

run_cmd attribute.register ``sym_to_pexpr_rule
run_cmd attribute.register ``sym_to_expr_rule
run_cmd attribute.register ``app_to_pexpr_keyed_rule
run_cmd attribute.register ``app_to_expr_keyed_rule
run_cmd attribute.register ``app_to_pexpr_unkeyed_rule
run_cmd attribute.register ``app_to_expr_unkeyed_rule

private meta def expr_of_mmexpr_app_keyed (env : trans_env) : mmexpr → list mmexpr → tactic expr
| (sym hd) args :=
  do expr_db ← caching_user_attribute.get_cache app_to_expr_keyed_rule,
     tactic.first $ (find expr_db hd).for $ λ f, f env args
| _ _ := failed

private meta def expr_of_mmexpr_app_unkeyed (env : trans_env) (hd : mmexpr) (args : list mmexpr) : tactic expr :=
do expr_db ← caching_user_attribute.get_cache app_to_expr_unkeyed_rule,
   tactic.first (list.map (λ f : trans_env → mmexpr → list mmexpr → tactic expr, f env hd args) expr_db)

private meta def expr_of_mmexpr_app_decomp (env : trans_env) (expr_of_mmexpr : trans_env → mmexpr → tactic expr)
         (hd : mmexpr) (args : list mmexpr) : tactic expr := 
do hs ← expr_of_mmexpr env hd,
   args' ← monad.mapm (expr_of_mmexpr env) args,
   return $ expr.mk_app hs args'

private meta def expr_of_mmexpr_app (env : trans_env) (expr_of_mmexpr : trans_env → mmexpr → tactic expr)
         (m : mmexpr) (l : list mmexpr) : tactic expr :=
expr_of_mmexpr_app_keyed env m l <|> 
expr_of_mmexpr_app_unkeyed env m l <|> 
expr_of_mmexpr_app_decomp env expr_of_mmexpr m l

private meta def pexpr_of_mmexpr_app_keyed (env : trans_env) : mmexpr → list mmexpr → tactic pexpr
| (sym hd) args := 
  do expr_db ← caching_user_attribute.get_cache app_to_pexpr_keyed_rule,
     tactic.first $ (find expr_db hd).for $ λ f, f env args
| _ _ := failed


private meta def pexpr_of_mmexpr_app_unkeyed (env : trans_env) (hd : mmexpr) (args : list mmexpr) : tactic pexpr := 
do expr_db ← caching_user_attribute.get_cache app_to_pexpr_unkeyed_rule,
   tactic.first (list.map (λ f : trans_env → mmexpr → list mmexpr → tactic pexpr, f env hd args) expr_db)

private meta def pexpr_of_mmexpr_app_decomp (env : trans_env) (pexpr_of_mmexpr : trans_env → mmexpr → tactic pexpr)
         (hd : mmexpr) (args : list mmexpr) : tactic pexpr := 
do hs ← pexpr_of_mmexpr env hd,
   args' ← monad.mapm (pexpr_of_mmexpr env) args,
   return $ pexpr_mk_app hs args'

private meta def pexpr_of_mmexpr_app (env : trans_env) (pexpr_of_mmexpr : trans_env → mmexpr → tactic pexpr)
         (m : mmexpr) (l : list mmexpr) : tactic pexpr :=
pexpr_of_mmexpr_app_keyed env m l <|> 
pexpr_of_mmexpr_app_unkeyed env m l <|> 
pexpr_of_mmexpr_app_decomp env pexpr_of_mmexpr m l

private meta def find_in_env (env : trans_env) (sym : string) : tactic expr :=
match rb_map.find env sym with
| some e := return e
| none   := failed
end

/--
expr_of_mmexpr env m will attempt to translate m to an expr, using translation rules found by
the attribute manager. env maps symbols (representing bound variables) to placeholder exprs.
-/
meta def expr_of_mmexpr : trans_env → mmexpr → tactic expr
| env (sym s)       := find_in_env env s <|> 
  do expr_db ← caching_user_attribute.get_cache sym_to_expr_rule,
     match find expr_db s with
     | (h :: t) := return h
     | []       := fail ("Couldn't find translation for sym \"" ++ s ++ "\"")
     end
| env (mstr s)      := return (string.reflect s)--to_expr (_root_.quote s)
| env (mreal r)     := return (reflect r)
| env (app hd args) := expr_of_mmexpr_app env expr_of_mmexpr hd args 
| env (mint i)      := failed

private meta def pexpr_of_mmexpr_aux (env : trans_env) 
         (pexpr_of_mmexpr : trans_env → mmexpr → tactic pexpr) :  mmexpr → tactic pexpr
| (sym s)   := 
  do expr_db ← caching_user_attribute.get_cache sym_to_pexpr_rule,
     match find expr_db s with
     | (h :: t) := return h
     | []       := fail ("Couldn't find translation for sym \"" ++ s ++ "\"")
     end
| (mint i ) := return $ pexpr_of_int i
| (app hd args) := pexpr_of_mmexpr_app env pexpr_of_mmexpr hd args 
| (mstr s)   := fail "unreachable, str case shouldn't reach pexpr_of_mmexpr_aux"
| (mreal r) := fail "unreachable, real case shouldn't reach pexpr_of_mmexpr_aux"

/--
pexpr_of_mmexpr env m will attempt to translate m to a pexpr, using translation rules found by
the attribute manager. env maps symbols (representing bound variables) to placeholder exprs.
-/
meta def pexpr_of_mmexpr : trans_env → mmexpr → tactic pexpr := 
λ env m, (do e ← expr_of_mmexpr env m, return ```(%%e)) <|>
         (pexpr_of_mmexpr_aux env pexpr_of_mmexpr m)

end translation

section unreflect

meta def level_of_mmexpr : mmexpr → tactic level 
| (sym "LeanZeroLevel") := return $ level.zero
| (app (sym "LeanLevelSucc") [m])      := do m' ← level_of_mmexpr m, return $ level.succ m'
| (app (sym "LeanLevelMax") [m1, m2])  := 
  do m1' ← level_of_mmexpr m1, 
     m2' ← level_of_mmexpr m2, 
     return $ level.max m1' m2'
| (app (sym "LeanLevelIMax") [m1, m2]) := 
  do m1' ← level_of_mmexpr m1, 
     m2' ← level_of_mmexpr m2, 
     return $ level.imax m1' m2'
| (app (sym "LeanLevelParam") [mstr s]) := return $ level.param s
| (app (sym "LeanLevelMeta") [mstr s])  := return $ level.mvar s
| _ := failed

meta def level_list_of_mmexpr : mmexpr → tactic (list level) 
| (sym "LeanLevelListNil")               := return []
| (app (sym "LeanLevelListCons") [h, t]) := 
  do h' ← level_of_mmexpr h, 
     t' ← level_list_of_mmexpr t,
     return $ h' :: t'
| _ := failed

meta def name_of_mmexpr : mmexpr → tactic name 
| (sym "LeanNameAnonymous")                 := return $ name.anonymous
| (app (sym "LeanNameMkString") [mstr s, m]) := 
  do n ← name_of_mmexpr m, return $ name.mk_string s n
| (app (sym "LeanNameMkNum") [mint i, m])   := 
  do n ← name_of_mmexpr m, return $ name.mk_numeral (unsigned_of_int i) n
| _ := failed

meta def binder_info_of_mmexpr : mmexpr → tactic binder_info 
| (sym "BinderInfoDefault")        := return $ binder_info.default 
| (sym "BinderInfoImplicit")       := return $ binder_info.implicit 
| (sym "BinderInfoStrictImplicit") := return $ binder_info.strict_implicit
| (sym "BinderInfoInstImplicit")   := return $ binder_info.inst_implicit
| (sym "BinderInfoOther")          := return $ binder_info.aux_decl
| _ := failed
end unreflect

section transl_expr_instances

@[app_to_expr_keyed]
meta def mmexpr_var_to_expr : app_trans_expr_keyed_rule :=
⟨"LeanVar", 
λ _ args, match args with
| [mint i] := return $ var (i.nat_abs)
| _        := failed
end⟩ 

@[app_to_expr_keyed]
meta def mmexpr_sort_to_expr : app_trans_expr_keyed_rule :=
⟨"LeanSort",
λ _ args, match args with
| [m] := do lvl ← level_of_mmexpr m, return $ sort lvl
| _   := failed
end⟩

@[app_to_expr_keyed]
meta def mmexpr_const_to_expr : app_trans_expr_keyed_rule :=
⟨"LeanConst",
λ _ args, match args with
| [nm, lvls] := do nm' ← name_of_mmexpr nm, lvls' ← level_list_of_mmexpr lvls, return $ const nm' lvls'
| _          := failed
end⟩

@[app_to_expr_keyed]
meta def mmexpr_mvar_to_expr : app_trans_expr_keyed_rule :=
⟨"LeanMetaVar",
λ env args, match args with
| [nm, tp] := do nm' ← name_of_mmexpr nm, tp' ← expr_of_mmexpr env tp, return $ mvar nm' tp'
| _        := failed
end⟩

@[app_to_expr_keyed]
meta def mmexpr_local_to_expr : app_trans_expr_keyed_rule :=
⟨"LeanLocal",
λ env args, match args with
| [nm, ppnm, bi, tp] := 
  do nm' ← name_of_mmexpr nm, 
     ppnm' ← name_of_mmexpr ppnm, 
     bi' ← binder_info_of_mmexpr bi, 
     tp' ← expr_of_mmexpr env tp, 
     return $ expr.local_const nm' ppnm' bi' tp'
| _ := failed
end⟩

@[app_to_expr_keyed]
meta def mmexpr_app_to_expr : app_trans_expr_keyed_rule :=
⟨"LeanApp",
λ env args, match args with
| [hd, bd] := do hd' ← expr_of_mmexpr env hd, bd' ← expr_of_mmexpr env bd, return $ expr.app hd' bd'
| _        := failed
end⟩

@[app_to_expr_keyed]
meta def mmexpr_lam_to_expr : app_trans_expr_keyed_rule :=
⟨"LeanLambda",
λ env args, match args with
| [nm, bi, tp, bd] :=
  do nm' ← name_of_mmexpr nm, 
     bi' ← binder_info_of_mmexpr bi, 
     tp' ← expr_of_mmexpr env tp,
     bd' ← expr_of_mmexpr env bd,
     return $ lam nm' bi' tp' bd'
| _   := failed
end⟩

@[app_to_expr_keyed]
meta def mmexpr_pi_to_expr : app_trans_expr_keyed_rule :=
⟨"LeanPi",
λ env args, match args with
| [nm, bi, tp, bd] := 
  do nm' ← name_of_mmexpr nm, 
     bi' ← binder_info_of_mmexpr bi, 
     tp' ← expr_of_mmexpr env tp,
     bd' ← expr_of_mmexpr env bd,
     return $ lam nm' bi' tp' bd'
| _ := failed
end⟩

meta def pexpr_fold_op_aux (op : pexpr) : pexpr → list pexpr → pexpr
| e [] := e
| e (h::t) := pexpr_fold_op_aux ```(%%op %%e %%h) t

meta def pexpr_fold_op (dflt op : pexpr) : list pexpr → pexpr
| [] := dflt
| [h] := h
| (h::t) := pexpr_fold_op_aux op h t

-- pexpr instances

@[app_to_pexpr_keyed]
meta def add_to_pexpr : app_trans_pexpr_keyed_rule :=
⟨"Plus", 
λ env args, do args' ← monad.for args (pexpr_of_mmexpr env), return $ pexpr_fold_op ```(0) ```(has_add.add) args'⟩

@[app_to_pexpr_keyed]
meta def mul_to_pexpr : app_trans_pexpr_keyed_rule :=
⟨"Times", 
λ env args, do args' ← monad.for args (pexpr_of_mmexpr env), return $ pexpr_fold_op ```(1) ```(has_mul.mul) args'⟩

@[app_to_pexpr_keyed]
meta def list_to_pexpr : app_trans_pexpr_keyed_rule := 
⟨"List", λ env args, 
         do args' ← monad.for args (pexpr_of_mmexpr env), 
            return $ list.foldr (λ h t, ```(%%h :: %%t)) ```([]) args'⟩


meta def pexpr.to_raw_expr : pexpr → expr
| (var n)                     := var n
| (sort l)                    := sort l
| (const nm ls)               := const nm ls
| (mvar n e)                  := mvar n (pexpr.to_raw_expr e)
| (local_const nm ppnm bi tp) := local_const nm ppnm bi (pexpr.to_raw_expr tp)
| (app f a)                   := app (pexpr.to_raw_expr f) (pexpr.to_raw_expr a)
| (lam nm bi tp bd)           := lam nm bi (pexpr.to_raw_expr tp) (pexpr.to_raw_expr bd)
| (pi nm bi tp bd)            := pi nm bi (pexpr.to_raw_expr tp) (pexpr.to_raw_expr bd)
| (elet nm tp df bd)          := elet nm (pexpr.to_raw_expr tp) (pexpr.to_raw_expr df) (pexpr.to_raw_expr bd)
| (macro md l)                := macro md (l.map pexpr.to_raw_expr)

meta def pexpr.of_raw_expr : expr → pexpr
| (var n)                     := var n
| (sort l)                    := sort l
| (const nm ls)               := const nm ls
| (mvar n e)                  := mvar n (pexpr.of_raw_expr e)
| (local_const nm ppnm bi tp) := local_const nm ppnm bi (pexpr.of_raw_expr tp)
| (app f a)                   := app (pexpr.of_raw_expr f) (pexpr.of_raw_expr a)
| (lam nm bi tp bd)           := lam nm bi (pexpr.of_raw_expr tp) (pexpr.of_raw_expr bd)
| (pi nm bi tp bd)            := pi nm bi (pexpr.of_raw_expr tp) (pexpr.of_raw_expr bd)
| (elet nm tp df bd)          := elet nm (pexpr.of_raw_expr tp) (pexpr.of_raw_expr df) (pexpr.of_raw_expr bd)
| (macro md l)                := macro md (l.map pexpr.of_raw_expr)


meta def mk_local_const_placeholder (n : name) : expr :=
let t := pexpr.mk_placeholder in
local_const n n binder_info.default (pexpr.to_raw_expr t)


private meta def sym_to_lcp : mmexpr → tactic (string × expr)
| (sym s) := return $ (s, mk_local_const_placeholder s)
| _ := failed

/-
meta def pexpr.lift_vars : pexpr → pexpr
| (var n) := var (n+1)
| (mvar n e) := mvar n (pexpr.lift_vars e)
| (local_const nm ppnm bi tp) := local_const nm ppnm bi (pexpr.lift_vars tp)
| (app f a) := app (pexpr.lift_vars f) (pexpr.lift_vars a)
| (lam nm bi tp bd) := lam nm bi (pexpr.lift_vars tp) (pexpr.lift_vars bd)
| (pi nm bi tp bd) := pi nm bi (pexpr.lift_vars tp) (pexpr.lift_vars bd)
| (elet nm tp df bd) := elet nm (pexpr.lift_vars tp) (pexpr.lift_vars df) (pexpr.lift_vars bd)
| (macro md l) := macro md (l.map pexpr.lift_vars)
| p := p

meta def pexpr.replace (old new : pexpr) : pexpr → pexpr
| (mvar n e) := mvar n (pexpr.lift_vars e)
| (local_const nm ppnm bi tp) := local_const nm ppnm bi (pexpr.lift_vars tp)
| (app f a) := app (pexpr.lift_vars f) (pexpr.lift_vars a)
| (lam nm bi tp bd) := lam nm bi (pexpr.lift_vars tp) (pexpr.lift_vars bd)
| (pi nm bi tp bd) := pi nm bi (pexpr.lift_vars tp) (pexpr.lift_vars bd)
| (elet nm tp df bd) := elet nm (pexpr.lift_vars tp) (pexpr.lift_vars df) (pexpr.lift_vars bd)
| (macro md l) := macro md (l.map pexpr.lift_vars)
| p := if p = old then new else p
-/

meta def mk_lambdas (l : list expr) (b : pexpr) : pexpr :=
pexpr.of_raw_expr (lambdas l (pexpr.to_raw_expr b))

meta def mk_lambda' (x : expr) (b : pexpr) : pexpr :=
pexpr.of_raw_expr (lambdas [x] (pexpr.to_raw_expr b))


/-
No longer needed, now that nested inductive bug is fixed
@[app_to_pexpr_keyed]
meta def function_to_pexpr : app_trans_pexpr_keyed_rule :=
⟨"Function",
λ env args, match args with
| [v1, bd] :=
  match v1 with
  | sym x := do
    v ← return $ mk_local_const_placeholder x, 
    bd' ← pexpr_of_mmexpr (env^.insert x v) bd,
    return $ mk_lambda' v bd' 
  | app (sym "List") l := do
    vs ← monad.for l sym_to_lcp,
    bd' ← pexpr_of_mmexpr (env^.insert_list vs) bd,
    return $ mk_lambdas (list.map prod.snd vs) bd'
  | _ := failed
  end
| _ := failed
end⟩-/

@[app_to_pexpr_keyed]
meta def function_to_pexpr : app_trans_pexpr_keyed_rule :=
⟨"Function",
λ env args, match args with
| [sym x, bd] := 
  do v ← return $ mk_local_const_placeholder x, 
     bd' ← pexpr_of_mmexpr (env.insert x v) bd,
     return $ mk_lambda' v bd' 
| [app (sym "List") l, bd] :=
  do vs ← monad.for l sym_to_lcp,
     bd' ← pexpr_of_mmexpr (env.insert_list vs) bd,
     return $ mk_lambdas (list.map prod.snd vs) bd'
| _ := failed
end⟩

@[sym_to_pexpr]
meta def rat_to_pexpr : sym_trans_pexpr_rule :=
⟨"Rational", ```(has_div.div)⟩ 


end transl_expr_instances
end mathematica

-- user-facing tactics
namespace tactic
namespace mathematica
open mathematica

private meta def mk_get_cmd (path : string) : string :=
"Get[\"" ++ path ++ "\",Path->{\""++extras_path++"\"}];"

/--
load_file path will load the file found at path into Mathematica.
The declarations will persist until the kernel is restarted.
-/
meta def load_file (path : string) : tactic unit :=
execute_global (mk_get_cmd path) >> return ()

/--
run_command_on cmd e reflects e into Mathematica syntax, applies cmd to this reflection,
evaluates this in Mathematica, and attempts to translate the result to a pexpr.
-/
meta def run_command_on (cmd : string → string) (e : expr) : tactic pexpr := 
do rval ← execute $ cmd $ form_of_expr e,
   rval' ← eval_expr mmexpr rval,
   pexpr_of_mmexpr trans_env.empty rval'

/--
run_command_on_using cmd e path reflects e into Mathematica syntax, applies cmd to this reflection,
evaluates this in Mathematica after importing the file at path, and attempts to translate the result to a pexpr.
-/
meta def run_command_on_using (cmd : string → string) (e : expr) (path : string) : tactic pexpr := 
run_command_on (λ s, mk_get_cmd path ++ cmd s) e

meta def run_command_on_2 (cmd : string → string → string) (e1 e2 : expr) : tactic pexpr :=
do rval ← execute $ cmd (form_of_expr e1) (form_of_expr e2),
   rval' ← eval_expr mmexpr rval,
   pexpr_of_mmexpr trans_env.empty rval'

/--
run_command_on_2_using cmd e1 e2 reflects e1 and e2 into Mathematica syntax, 
applies cmd to these reflections, evaluates this in Mathematica after importing the file at path, 
and attempts to translate the result to a pexpr.
-/
meta def run_command_on_2_using (cmd : string → string → string) (e1 e2 : expr) (path : string) :
     tactic pexpr := 
run_command_on_2 (λ s1 s2, mk_get_cmd path ++ cmd s1 s2) e1 e2

private def sep_string : list string → string
| [] := ""
| [s] := s
| (h::t) := h ++ ", " ++ sep_string t

/--
run_command_on_list cmd l reflects each element of l into Mathematica syntax, 
applies cmd to a Mathematica list of these reflections,
evaluates this in Mathematica, and attempts to translate the result to a pexpr.
-/
meta def run_command_on_list (cmd : string → string) (l : list expr) : tactic pexpr :=
let lvs := "{" ++ (sep_string $ l.map form_of_expr) ++ "}" in
do rval ← execute $ cmd lvs,
   rval' ← eval_expr mmexpr rval,
   pexpr_of_mmexpr trans_env.empty rval'


meta def run_command_on_list_using (cmd : string → string) (l : list expr) (path : string) : tactic pexpr :=
let lvs := "{" ++ (sep_string $ l.map form_of_expr) ++ "}" in
do rval ← execute $ mk_get_cmd path ++ cmd lvs,
   rval' ← eval_expr mmexpr rval,
   pexpr_of_mmexpr trans_env.empty rval'

end mathematica
end tactic
