LeanName[s_String] := LeanNameMkString[s, LeanNameAnonymous];
LeanName[s_String, t_String] := LeanNameMkString[t, LeanName[s]];
LeanName[i_Int] := LeanNameMkNum[i, LeanNameAnonymous];
(*LeanAddSym[lvl_, tp_, tc_]:=LeanApp[LeanApp[LeanConst[LeanName["add"],lvl],tp ], tc]*)

UnderscoreName[LeanNameMkString[s_String, t_]] := 
  LeanNameMkString[s <> "_1", t];
UnderscoreName[LeanNameMkNum[i_Int, t_]] := 
  LeanNameMkNum[1, LeanNameMkNum[i, t]];
StringOfName[LeanNameAnonymous] := "";
StringOfName[LeanNameMkString[s_String, LeanNameAnonymous]] := s;
StringOfName[LeanNameMkString[s_String, t_]] := 
  s <> "." <> StringOfName[t];
StringOfName[LeanNameMkNum[i_Int, LeanNameAnonymous]] := ToString[i];
StringOfName[LeanNameMkNum[i_Int, t_]] := 
  ToString[i] <> "." <> StringOfName[t];


SetAttributes[makeFunction, HoldAll]
makeFunction[string_String, body_] := 
  makeFunction[string, body, False];
makeFunction[string_String, body_makeFunction, evalQ_] := 
 With[{eval = body}, makeFunction[string, eval, evalQ]]
makeFunction[string_String, body_, evalQ_] := 
  With[{symbol = Symbol[string], head = If[evalQ, List, Hold]}, 
   Apply[Function, 
    ReplaceAll[head[symbol, body], LeanVar[string] -> symbol]]];

FunSimp[expr_] := (expr //. {LeanLambda[LeanVar[x_], _, y_] -> 
     makeFunction[x, y]})

EvaluateFunctionBody[HoldPattern[Function[x_, body_]]] := 
  Apply[Function, {x, EvaluateFunctionBody[body]}];
EvaluateFunctionBody[body_] := body;

LeftOperatorQ[Plus] := True;
LeftOperatorQ[Times] := True;
LeftOperatorQ[And] := True;
LeftOperatorQ[Or] := True;

Lean[Plus] := LeanAdd;
Lean[Times] := LeanMul;
Lean[And] := LeanAnd;
Lean[Or] := LeanOr;

ArithConvert[op_?LeftOperatorQ[x__, y_]] := 
  Lean[op][ArithConvert[op[x]], ArithConvert[y]];
ArithConvert[op_?RightOperatorQ[x_, y__]] := 
  Lean[op][ArithConvert[x], ArithConvert[op[y]]];
ArithConvert[f_[args__]] := Apply[f, Map[ArithConvert, {args}]];
ArithConvert[x_] := x;

ListConvert[List[]] := LeanListNil;
ListConvert[List[a_, x___]] := LeanListCons[a, ListConvert[List[x]]];
ListConvert[e_] := e;


LeanForm[LeanApp[
   LeanApp[LeanApp[
     LeanApp[LeanConst[LeanName["has_add", "add"], _], _], _], x_], 
   y_], v_] := Inactive[Plus][LeanForm[x, v], LeanForm[y, v]]

LeanForm[LeanApp[
   LeanApp[LeanApp[
     LeanApp[LeanConst[LeanName["has_mul", "mul"], _], _], _], x_], 
   y_], v_] := Inactive[Times][LeanForm[x, v], LeanForm[y, v]]

LeanForm[LeanApp[
   LeanApp[LeanApp[
     LeanApp[LeanConst[LeanName["has_div", "div"], _], _], _], x_], 
   y_], v_] := Inactive[Divide][LeanForm[x, v], LeanForm[y, v]]

LeanForm[LeanApp[
   LeanApp[LeanApp[
     LeanApp[LeanConst[LeanName["has_sub", "sub"], _], _], _], x_], 
   y_], v_] := Inactive[Subtract][LeanForm[x, v], LeanForm[y, v]]

LeanForm[LeanApp[
   LeanApp[LeanApp[LeanConst[LeanName["has_neg", "neg"], _], _], _], 
   x_], v_] := Inactive[Times][-1, LeanForm[x, v]]
LeanForm[LeanApp[
   LeanApp[LeanApp[LeanApp[LeanConst[LeanName["add"], _], _], _], x_],
    y_], v_] := Inactive[Plus][LeanForm[x, v], LeanForm[y, v]]

LeanForm[LeanApp[
   LeanApp[LeanApp[LeanApp[LeanConst[LeanName["mul"], _], _], _], x_],
    y_], v_] := Inactive[Times][LeanForm[x, v], LeanForm[y, v]]

LeanForm[LeanApp[
   LeanApp[LeanApp[LeanApp[LeanConst[LeanName["div"], _], _], _], x_],
    y_], v_] := Inactive[Divide][LeanForm[x, v], LeanForm[y, v]]

LeanForm[LeanApp[
   LeanApp[LeanApp[LeanApp[LeanConst[LeanName["sub"], _], _], _], x_],
    y_], v_] := Inactive[Subtract][LeanForm[x, v], LeanForm[y, v]]

LeanForm[LeanApp[
   LeanApp[LeanApp[LeanConst[LeanName["neg"], _], _], _], x_], v__] :=
  Inactive[Times][-1, LeanForm[x, v]]

LeanForm[LeanApp[
   LeanApp[LeanApp[LeanApp[LeanConst[LeanName["pow_nat"], _], _], _], 
    x_], y_], v_] := Inactive[Power][LeanForm[x, v], LeanForm[y, v]]

LeanForm[LeanApp[LeanApp[LeanConst[LeanName["and"], _], x_], y_], 
  v_] := Inactive[And][LeanForm[x, v], LeanForm[y, v]]

LeanForm[LeanApp[LeanApp[LeanConst[LeanName["or"], _], x_], y_], v_] :=
  Inactive[Or][LeanForm[x, v], LeanForm[y, v]]

LeanForm[LeanApp[LeanApp[LeanConst[LeanName["implies"], _], x_], y_], 
  v_] := Inactive[Implies][LeanForm[x, v], LeanForm[y, v]]

LeanForm[LeanApp[LeanConst[LeanName["not"], _], x_], v_] := 
 Inactive[Not][LeanForm[x, v]]

LeanForm[LeanApp[LeanApp[LeanConst[LeanName["one"], _], _], _], 
  v_] := 1

LeanForm[LeanApp[LeanApp[LeanConst[LeanName["zero"], _], _], _], 
  v_] := 0

LeanForm[LeanApp[
   LeanApp[LeanConst[LeanName["has_one", "one"], _], _], _], v_] := 1

LeanForm[LeanApp[
   LeanApp[LeanConst[LeanName["has_zero", "zero"], _], _], _], v_] := 0

LeanForm[LeanApp[
   LeanApp[LeanApp[LeanConst[LeanName["bit0"], _], _], _], t_], v_] :=
  2*LeanForm[t, v]

LeanForm[LeanApp[
   LeanApp[LeanApp[LeanApp[LeanConst[LeanName["bit1"], _], _], _], _],
    t_], v_] := 2*LeanForm[t, v] + 1

LeanForm[LeanApp[LeanConst[LeanName["list", "nil"], _], _], v_] := {}

LeanForm[LeanApp[
   LeanApp[LeanApp[LeanConst[LeanName["list", "cons"], _], _], h_], 
   t_], v_] := Prepend[LeanForm[t, v], LeanForm[h, v]]

LeanForm[LeanApp[
   LeanApp[LeanApp[LeanApp[LeanConst[LeanName["lt"], _], _], _], x_], 
   y_], v_] := Inactive[Less][LeanForm[x, v], LeanForm[y, v]]

LeanForm[LeanApp[
   LeanApp[LeanApp[LeanApp[LeanConst[LeanName["le"], _], _], _], x_], 
   y_], v_] := Inactive[LessEqual][LeanForm[x, v], LeanForm[y, v]]

LeanForm[LeanApp[
   LeanApp[LeanApp[LeanApp[LeanConst[LeanName["gt"], _], _], _], x_], 
   y_], v_] := Inactive[Greater][LeanForm[x, v], LeanForm[y, v]]

LeanForm[LeanApp[
   LeanApp[LeanApp[LeanApp[LeanConst[LeanName["ge"], _], _], _], x_], 
   y_], v_] := Inactive[GreaterEqual][LeanForm[x, v], LeanForm[y, v]]

LeanForm[LeanApp[
   LeanApp[LeanApp[
     LeanApp[LeanConst[LeanName["has_lt", "lt"], _], _], _], x_], y_],
   v_] := Inactive[Less][LeanForm[x, v], LeanForm[y, v]]

LeanForm[LeanApp[
   LeanApp[LeanApp[
     LeanApp[LeanConst[LeanName["has_le", "le"], _], _], _], x_], y_],
   v_] := Inactive[LessEqual][LeanForm[x, v], LeanForm[y, v]]

LeanForm[LeanApp[
   LeanApp[LeanApp[
     LeanApp[LeanConst[LeanName["has_gt", "gt"], _], _], _], x_], y_],
   v_] := Inactive[Greater][LeanForm[x, v], LeanForm[y, v]]

LeanForm[LeanApp[
   LeanApp[LeanApp[
     LeanApp[LeanConst[LeanName["has_ge", "ge"], _], _], _], x_], y_],
   v_] := Inactive[GreaterEqual][LeanForm[x, v], LeanForm[y, v]]


LeanForm[LeanSort[l_], v_] := LeanSort[l]

LeanForm[LeanConst[a_, b_], v_] := LeanConst[a, b]

LeanForm[LeanMetaVar[a_, b_], v_] := LeanMetaVar[a, b]

(*LeanForm[LeanApp[f_, e_],v__] := LeanForm[f, v][LeanForm[e, v]]*)

LeanForm[LeanLocal[n_, pn_, b_, t_], v_] := LeanLocal[n, pn, b, t]

LeanForm[LeanPi[nm_, bi_, tp_, bod_], v_] := LeanPi[nm, bi, tp, bod]

LeanForm[LeanLambda[nm_, bi_, tp_, bd_], v_] := 
 If[MemberQ[v, Symbol[nm]], 
  LeanForm[LeanLambda[UnderscoreName[nm], bi, tp, bd], v], 
  Apply[Function, 
   List[Symbol[StringOfName[nm]], 
    LeanForm[bd, Prepend[v, Symbol[nm]]]]]]

LeanForm[LeanApp[LeanLambda[nm_, bi_, tp_, bd_], e_], v_] := 
 LeanForm[LeanLambda[nm, bi, tp, bd], v][LeanForm[e]]

LeanForm[LeanVar[a_], v_] := v[[a + 1]]

LeanForm[e_] := LeanForm[e, {}]