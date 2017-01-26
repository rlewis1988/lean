import .tactic
open expr string level name binder_info

--meta constant pexpr.abstract_local : pexpr → name → pexpr

meta instance : has_to_format unsigned := ⟨λ i, fin.rec_on i (λ val is_lt, val)⟩

meta def name_to_qstring (nm : name) : string := "\"" ++ name.to_string nm ++ "\""

meta def mathematica_form_of_name : name → string
| anonymous         := "LeanNameAnonymous"
| (mk_string s nm)  := "LeanNameMkString[\"" ++ s ++ "\", " ++ mathematica_form_of_name nm ++ "]"
| (mk_numeral i nm) := "LeanNameMkNum[" ++ to_string i ++ ", " ++ mathematica_form_of_name nm ++ "]"

meta def mathematica_form_of_lvl : level → string
| zero              := "LeanZeroLevel"
| (succ l)          := "LeanLevelSucc[" ++ mathematica_form_of_lvl l ++ "]"
| (level.max l1 l2) := "LeanLevelMax[" ++ mathematica_form_of_lvl l1 ++ ", " ++ mathematica_form_of_lvl l2 ++ "]"
| (imax l1 l2)      := "LeanLevelIMax[" ++ mathematica_form_of_lvl l1 ++ ", " ++ mathematica_form_of_lvl l2 ++ "]"
| (param nm)        := "LeanLevelParam[̈" ++ name_to_qstring nm ++ "]"
| (global nm)       := "LeanLevelGlobal[" ++ name_to_qstring nm ++ "]"
| (mvar nm)         := "LeanLevelMeta[" ++ name_to_qstring nm ++ "]"

meta def mathematica_form_of_lvl_list : list level → string
| []       := "LeanLevelListNil"
| (h :: t) := "LeanLevelListCons[" ++ mathematica_form_of_lvl h ++ ", " ++ mathematica_form_of_lvl_list t ++ "]"

meta def mathematica_form_of_binder_info : binder_info → string
| binder_info.default := "BinderInfoDefault"
| implicit            := "BinderInfoImplicit"
| strict_implicit     := "BinderInfoStrictImplicit"
| inst_implicit       := "BinderInfoInstImplicit"
| other               := "BinderInfoOther"

inductive signed_num : Type 
| pos : num → signed_num
| neg_succ : num → signed_num

def int_of_signed_num : signed_num → int
| (signed_num.pos k) := int.of_nat (nat.of_num k)
| (signed_num.neg_succ k) := int.neg_succ_of_nat (nat.of_num k)

meta def expand_let : expr → expr
| (elet nm tp val bod) := expr.replace bod (λ e n, match e with |var n := some val | _ := none end)
| e := e

meta def expand_let_rec : expr → expr
| (elet nm tp val bod) := expr.replace (expand_let_rec bod) (λ e n, match e with |var n := some val | _ := none end)
| (mvar nm tp) := mvar nm (expand_let_rec tp)
| (local_const nm ppnm bi tp) := local_const nm ppnm bi (expand_let_rec tp)
| (app f e) := app (expand_let_rec f) (expand_let_rec e)
| (lam nm bi tp bod) := lam nm bi (expand_let_rec tp) (expand_let_rec bod)
| (pi nm bi tp bod) := pi nm bi (expand_let_rec tp) (expand_let_rec bod)
| e := e

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

-- if even n then `(bit0 %%(pexpr_of_nat (n/2 + 1))) else `(bit1 %%(pexpr_of_nat ((n+1) / 2)))


meta def pexpr_of_signed_num : signed_num → pexpr
| (signed_num.pos k) := pexpr_of_num k
| (signed_num.neg_succ k) := `(-(%%(pexpr_of_num (k+1))))

meta def pexpr_of_char : char → pexpr
| (fin.mk k l) := `((fin.mk %%(pexpr_of_nat k) dec_trivial : char))

meta def pexpr_of_string : string → pexpr
| [] := `(list.nil)
| (h :: t) := `(list.cons %%(pexpr_of_char h) %%(pexpr_of_string t))

meta def int_to_format (i : int) : format :=
int.rec_on i (λ k, to_fmt k) (λ k, "-(1+" ++ to_fmt k ++ ")")

meta def htfi : has_to_format int := ⟨int_to_format⟩
local attribute [instance] htfi
/-inductive mmexpr : Type
| sym  : string → mmexpr
| str  : string → mmexpr
| int  : int → mmexpr -- includes a pexpr representation
| real : int → mmexpr -- this obviously isn't right
| rat  : int → int → mmexpr
| comp : int → int → mmexpr -- this obviously isn't right
| app  : mmexpr → list mmexpr → mmexpr-/

meta inductive mmexpr : Type
| sym  : string → mmexpr
| str  : string → mmexpr
| mint  : signed_num → mmexpr -- includes a pexpr representation
--| real : pexpr → mmexpr -- this obviously isn't right
--| rat  : pexpr → pexpr → mmexpr
--| comp : pexpr → pexpr → mmexpr -- this obviously isn't right
| app  : mmexpr → list mmexpr → mmexpr

-- wolfram
namespace tactic
--meta constant factor        : expr → tactic pexpr
--meta constant factor_int    : nat → tactic pexpr
--meta constant factor_matrix : expr → tactic expr
--meta constant wl_simplify   : expr → tactic pexpr
meta constant wl_execute_str : string → tactic expr
--meta constant wl_execute_expr : expr → string → tactic pexpr
--meta constant wl_execute_on_expr_using : string → expr → string → tactic pexpr
--meta constant wl_execute_on_expr : string → expr → tactic pexpr
--meta constant translate_to_wl_test : expr → tactic unit
end tactic

open mmexpr tactic

meta def mmexpr_list_to_format (f : mmexpr → format) : list mmexpr → format
| [] := to_fmt ""
| [h] := f h
| (h :: t) := f h ++ ", " ++ mmexpr_list_to_format t

meta def mmexpr_to_format : mmexpr → format
| (sym s)     := to_fmt s
| (str s)     := to_fmt "\"" ++ to_fmt s ++ "\""
| (mint i) := to_fmt (int_of_signed_num i)
--| (real i)    := to_fmt "" --i
--| (rat i j)   := to_fmt "" --"(" ++ to_fmt i ++ "/" ++ to_fmt j ++ to_fmt ")"
--| (comp i j)  := to_fmt "" --"(" ++ to_fmt i ++ " + i*" ++ to_fmt j ++ to_fmt ")"
| (app e1 ls) := mmexpr_to_format e1 ++ to_fmt "[" ++ mmexpr_list_to_format mmexpr_to_format ls ++ to_fmt "]"


meta instance : has_to_format mmexpr := ⟨mmexpr_to_format⟩

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

meta instance mmexpr_level_list_nil : mmexpr_has_to_level_list (sym "LeanLevelListNil") :=
⟨_, []⟩

meta instance mmexpr_level_list_cons (h t : mmexpr) [mmexpr_has_to_level h] [mmexpr_has_to_level_list t] : mmexpr_has_to_level_list (app (sym "LeanLevelListCons") [h, t]) :=
⟨_, list.cons (level_of_mmexpr h) (level_list_of_mmexpr t)⟩

meta instance mmexpr_level_zero : mmexpr_has_to_level (sym "LeanZeroLevel") :=
⟨_, level.zero⟩

meta instance mmexpr_level_succ (m : mmexpr) [mmexpr_has_to_level m] : mmexpr_has_to_level (app (sym "LeanLevelSucc") [m]) :=
⟨_, level.succ (level_of_mmexpr m)⟩

meta instance mmexpr_level_max (m1 m2 : mmexpr) [mmexpr_has_to_level m1] [mmexpr_has_to_level m2] : mmexpr_has_to_level (app (sym "LeanLevelMax") [m1, m2]) :=
⟨_, level.max (level_of_mmexpr m1) (level_of_mmexpr m2)⟩

meta instance mmexpr_level_imax (m1 m2 : mmexpr) [mmexpr_has_to_level m1] [mmexpr_has_to_level m2] : mmexpr_has_to_level (app (sym "LeanLevelIMax") [m1, m2]) :=
⟨_, level.imax (level_of_mmexpr m1) (level_of_mmexpr m2)⟩

meta instance mmexpr_level_param (s : string) : mmexpr_has_to_level (app (sym "LeanLevelParam") [str s]) :=
⟨_, level.param s⟩

meta instance mmexpr_level_global (s : string) : mmexpr_has_to_level (app (sym "LeanLevelGlobal") [str s]) :=
⟨_, level.global s⟩

meta instance mmexpr_level_mvar(s : string) : mmexpr_has_to_level (app (sym "LeanLevelMeta") [str s]) :=
⟨_, level.mvar s⟩

meta instance mmexpr_name_anonymous : mmexpr_has_to_name (sym "LeanNameAnonymous") :=
⟨_, anonymous⟩

meta instance mmexpr_name_mk_string (s : string) (m : mmexpr) [mmexpr_has_to_name m] : mmexpr_has_to_name (app (sym "LeanNameMkString") [str s, m]) :=
⟨_, mk_string s (name_of_mmexpr m)⟩

meta instance mmexpr_name_mk_num (i : num) (m : mmexpr) [mmexpr_has_to_name m] : mmexpr_has_to_name (app (sym "LeanNameMkNum") [mint (signed_num.pos i), m]) :=
⟨_, mk_numeral (unsigned.of_nat (nat.of_num i)) (name_of_mmexpr m)⟩


meta def unsigned_of_signed_num (i : signed_num) : unsigned := 
signed_num.rec_on i (λ k, unsigned.of_nat (nat.of_num k)) (λ k, unsigned.of_nat (nat.of_num k))

meta instance mmexpr_has_to_expr_var (i : signed_num) : mmexpr_has_to_expr (app (sym "LeanVar") [mint i]) :=
⟨_, (var (unsigned_of_signed_num i))⟩

meta instance mmexpr_has_to_expr_sort (m : mmexpr) [mmexpr_has_to_level m] : mmexpr_has_to_expr (app (sym "LeanSort") [m]) :=
⟨_, sort (level_of_mmexpr m)⟩

meta instance mmexpr_has_to_expr_const (nm lvls : mmexpr) [mmexpr_has_to_name nm] [mmexpr_has_to_level_list lvls] : mmexpr_has_to_expr (app (sym "LeanConst") [nm, lvls]) := 
⟨_, const (name_of_mmexpr nm) (level_list_of_mmexpr lvls)⟩

meta instance mmexpr_has_to_expr_mvar (nm m : mmexpr) [mmexpr_has_to_name nm] [mmexpr_has_to_expr m] : mmexpr_has_to_expr (app (sym "LeanMetaVar") [nm, m]) :=
⟨_, mvar (name_of_mmexpr nm) (expr_of_mmexpr m)⟩

meta instance mmexpr_has_to_expr_local (nm ppnm bi tp : mmexpr) [mmexpr_has_to_name nm] [mmexpr_has_to_name ppnm] [mmexpr_has_to_binder_info bi] [mmexpr_has_to_expr tp] : mmexpr_has_to_expr (app (sym "LeanLocal") [nm,ppnm, bi, tp]) :=
⟨_, (expr.local_const (name_of_mmexpr nm) (name_of_mmexpr ppnm) (binder_info_of_mmexpr bi) (expr_of_mmexpr tp)) ⟩

meta instance mmexpr_has_to_expr_app (f e : mmexpr) [mmexpr_has_to_expr f] [mmexpr_has_to_expr e] : mmexpr_has_to_expr (app (sym "LeanApp") [f, e]) :=
⟨_, expr.app (expr_of_mmexpr f) (expr_of_mmexpr e)⟩

meta instance mmexpr_has_to_expr_lam (nm bi tp bd : mmexpr) [mmexpr_has_to_name nm] [mmexpr_has_to_binder_info bi] [mmexpr_has_to_expr tp] [mmexpr_has_to_expr bd] : mmexpr_has_to_expr (app (sym "LeanLambda") [nm, bi, tp, bd]) :=
⟨_, lam (name_of_mmexpr nm) (binder_info_of_mmexpr bi) (expr_of_mmexpr tp) (expr_of_mmexpr bd)⟩

meta instance mmexpr_has_to_expr_pi (nm bi tp bd : mmexpr) [mmexpr_has_to_name nm] [mmexpr_has_to_binder_info bi] [mmexpr_has_to_expr tp] [mmexpr_has_to_expr bd] : mmexpr_has_to_expr (app (sym "LeanPi") [nm, bi, tp, bd]) :=
⟨_, pi (name_of_mmexpr nm) (binder_info_of_mmexpr bi) (expr_of_mmexpr tp) (expr_of_mmexpr bd)⟩


meta instance mmexpr_has_to_pexpr_of_has_to_expr (m : mmexpr) [mmexpr_has_to_expr m] : mmexpr_has_to_pexpr m :=
⟨_, pexpr.of_expr (expr_of_mmexpr m)⟩


meta instance mmexpr_has_to_pexpr_plus (x y : mmexpr) [mmexpr_has_to_pexpr x] [mmexpr_has_to_pexpr y] : mmexpr_has_to_pexpr (app (sym "LeanAdd") [x, y]) :=
⟨_, `(%%(pexpr_of_mmexpr x) + %%(pexpr_of_mmexpr y))⟩

meta instance mmexpr_has_to_pexpr_times (x y : mmexpr) [mmexpr_has_to_pexpr x] [mmexpr_has_to_pexpr y] : mmexpr_has_to_pexpr (app (sym "LeanMul") [x, y]) :=
⟨_, `(%%(pexpr_of_mmexpr x) * %%(pexpr_of_mmexpr y))⟩

meta instance mmexpr_has_to_pexpr_list_nil : mmexpr_has_to_pexpr (sym "LeanListNil") :=
⟨_, `(list.nil)⟩

meta instance mmexpr_has_to_pexpr_list_cons (h t : mmexpr) [mmexpr_has_to_pexpr h] [mmexpr_has_to_pexpr t] : mmexpr_has_to_pexpr (app (sym "LeanListCons") [h, t]) :=
⟨_, `(list.cons %%(pexpr_of_mmexpr h) %%(pexpr_of_mmexpr t))⟩

/-meta def abstract_mmexpr_symbol (s : string) (new_s : mmexpr) : mmexpr → mmexpr
| (app e l) := app (abstract_mmexpr_symbol e) (list.map abstract_mmexpr_symbol l)
| (sym t)   := if s = t then new_s else sym t
| (str t)   := str t
| (mint i)  := mint i

meta instance mmexpr_has_to_pexpr_function (s : string) (m : mmexpr) [h : mmexpr_has_to_pexpr (abstract_mmexpr_symbol s (app (sym "LeanLocal") [str "MMVAR_s", str "MMVAR_s", (sym "BinderInfoDefault"), app (sym "LeanConst") [str "nat", sym "LeanLevelListNil"]]) m)] : mmexpr_has_to_pexpr (app (sym "Function") [sym s, m]) :=
⟨_, `(λ MMVAR_s, %%(@pexpr_of_mmexpr _ h))⟩
--⟨_, expr.abstract_local (@expr_of_mmexpr _ h) s⟩

meta example : abstract_mmexpr_symbol "x" (sym "y") (app (sym "Plus") [sym "x", sym "x"]) = app (sym "Plus") [sym "y", sym "y"] := begin

end

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



meta instance mmexpr_has_to_pexpr_int (i : signed_num) : mmexpr_has_to_pexpr (mint i) :=
⟨_, pexpr_of_signed_num i⟩

meta instance mmexpr_has_to_pexpr_string (s : string)  : mmexpr_has_to_pexpr (mmexpr.str s) :=
⟨_, pexpr_of_string s⟩

--meta constant run_mm_command_on_expr_using_core (cmd path : string) : tactic expr

meta def run_mm_command_on_expr (cmd : string → string) (e : expr) : tactic pexpr := do
 rval ← wl_execute_str $ cmd $ mathematica_form_of_expr e,
 trace "rval: ", trace rval,
 pexe ← to_expr `(pexpr_of_mmexpr %%rval),
 eval_expr pexpr pexe

meta def run_mm_command_on_expr_using (cmd : string → string) (e : expr) (path : string) : tactic pexpr := do
 rval ← wl_execute_str ("Get[\"" ++ path ++ "\"]; " ++ (cmd (mathematica_form_of_expr e))),
 trace "rval: ", trace rval,
 pexe ← to_expr `(pexpr_of_mmexpr %%rval),
 eval_expr pexpr pexe

exit

open tactic

--set_option trace.class_instances true

example : true = true := by do
 s ← to_expr `(λ x : ℕ, x),
 trace $ mathematica_form_of_expr s,
 reflexivity

--set_option pp.all true
def foo (x y z : ℕ) : true = true := by do
  s ← to_expr `(x + y),
  ex ← wl_execute_str (mathematica_form_of_expr s), --"Plus[2, 4, 220199]",
  trace ex,
  infer_type ex >>= trace,
 -- htpei ← to_expr `(mmexpr_has_to_pexpr %%ex) >>= mk_instance,
  --exm ← eval_expr mmexpr ex,
  --trace ("exm", exm),
  ex' ← to_expr `(pexpr_of_mmexpr %%ex),
  --let ex' := expr_of_mmexpr exm in do
  trace ex',
  infer_type ex' >>= trace,
  ex'' ← eval_expr pexpr ex',
  ex''' ← to_expr ex'', --`((%%ex'' : ℕ)),
  trace ex''',
  infer_type ex''' >>= trace, 
 reflexivity

