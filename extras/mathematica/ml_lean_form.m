toBinaryStringGeneral[expr_, headsToBinarize_List] := 
 Module[{res, headsA = Alternatives @@ headsToBinarize}, 
  Block[headsToBinarize, 
   res = expr //. (g : headsA)[argL1_, argL2_, argrestL__] :>
       g[g[argL1, argL2], argrestL];
   ToString[FullForm[res]]]]

toBS[expr_] := toBinaryStringGeneral[expr, {Plus, Times}]

listSimpRules = {
  List[a_, x__] -> ListCons[a, List[x]],
  List[a_] -> ListEnd[a],
  List[] -> ListNil
  };

ListSimp[expr_] := (expr //. listSimpRules)


SetAttributes[makeFunction, HoldAll]
makeFunction[string_String, body_] := makeFunction[string, body, False];
makeFunction[string_String, body_makeFunction, evalQ_] := 
 With[{eval = body}, makeFunction[string, eval, evalQ]]
makeFunction[string_String, body_, evalQ_] := 
  With[{symbol = Symbol[string], head = If[evalQ, List, Hold]}, 
   Apply[Function, 
    ReplaceAll[head[symbol, body], LeanVar[string] -> symbol]]];

FunSimp[expr_] := (expr //. {LeanLambda[LeanVar[x_], _, y_] -> makeFunction[x, y]})

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

arithsimp[op_?LeftOperatorQ[x__, y_]] := Lean[op][arithsimp[op[x]], arithsimp[y]];
arithsimp[op_?RightOperatorQ[x_, y__]] := Lean[op][arithsimp[x], arithsimp[op[y]]];
arithsimp[f_[args__]] := Apply[f, Map[arithsimp, {args}]];
arithsimp[x_] := x;

lfrules = {
   LeanVar[s_String] -> s,(*\[RuleDelayed]Style[s, 
   Blue, Italic],*)
   LeanConst[s_String] -> s
   };
LeanForm[expr_] := (expr //. lfrules)
ltrules = {
   LeanApp[
     LeanApp[LeanApp[LeanApp[LeanConst["has_add.add"], _], _], 
      x_], y_] -> Inactive[Plus][x, y],
   LeanApp[
     LeanApp[LeanApp[LeanApp[LeanConst["has_mul.mul"], _], _], 
      x_], y_] -> Inactive[Times][x, y],
   LeanApp[
     LeanApp[LeanApp[LeanApp[LeanConst["has_div.div"], _], _], 
      x_], y_] -> Inactive[Divide][x, y],
   LeanApp[
     LeanApp[LeanApp[LeanApp[LeanConst["has_sub.sub"], _], _], 
      x_], y_] -> Inactive[Subtract][x, y],
   LeanApp[LeanApp[LeanApp[LeanConst["has_neg.neg"], _], _], 
     x_] -> Inactive[Times][-1, x],
   LeanApp[LeanApp[LeanApp[LeanApp[LeanConst["pow_nat"], _], _], x_], y_] -> Inactive[Power][x, y],
     LeanApp[LeanApp[LeanApp[LeanApp[LeanConst["add"], _], _], 
      x_], y_] -> Inactive[Plus][x, y],
   LeanApp[
     LeanApp[LeanApp[LeanApp[LeanConst["mul"], _], _], 
      x_], y_] -> Inactive[Times][x, y],
   LeanApp[
     LeanApp[LeanApp[LeanApp[LeanConst["div"], _], _], 
      x_], y_] -> Inactive[Divide][x, y],
   LeanApp[
     LeanApp[LeanApp[LeanApp[LeanConst["sub"], _], _], 
      x_], y_] -> Inactive[Subtract][x, y],
   LeanApp[LeanApp[LeanApp[LeanConst["neg"], _], _], 
     x_] -> Inactive[Times][-1, x],
   LeanApp[LeanApp[LeanConst["and"], x_], y_] -> 
    Inactive[And][x, y],
   LeanApp[LeanApp[LeanConst["or"], x_], y_] -> 
    Inactive[Or][x, y],
   LeanApp[LeanApp[LeanConst["implies"], x_], y_] -> 
    Inactive[Implies][x, y],
   LeanApp[LeanConst["not"], x_] -> Inactive[Not][x],
   LeanPi[_, LeanType[_], x_] -> x,
   LeanPi[a_, _, x_] -> Inactive[ForAll][a, x],
   LeanApp[LeanApp[LeanConst["one"], _], _] -> 1,
   LeanApp[LeanApp[LeanConst["zero"], _], _] -> 0,
   LeanApp[LeanApp[LeanConst["has_one.one"], _], _] -> 1,
   LeanApp[LeanApp[LeanConst["has_zero.zero"], _], _] -> 0,
   LeanApp[LeanApp[LeanApp[LeanConst["bit0"], _], _], t_] -> 2*t,
   LeanApp[LeanApp[LeanApp[LeanApp[LeanConst["bit1"], _], _], _], t_] -> 2*t+1,
   LeanApp[LeanConst["list.nil"], _] -> {},
   LeanApp[LeanApp[LeanApp[LeanConst["list.cons"], _], h_], t_List] -> Join[{h}, t]
   };
LeanConvert[expr_] := (expr //. ltrules)
