
DirectIneq[GreaterEqual[p_, q_]] := q - p <= 0
DirectIneq[Greater[p_, q_]] := q - p < 0
DirectIneq[LessEqual[p_, q_]] := p - q <= 0
DirectIneq[Less[p_, q_]] := p - q <  0
DirectIneqs[l_] := Map[DirectIneq, l]

GetPolyPart[LessEqual[p_, q_]] := p
GetPolyPart[Less[p_, q_]] := p

DenScale[l_] := Apply[LCM, Map[Denominator, l]]
ScaleList[l_] := DenScale[l]*l

GenCoeffMatrix[l_] := 
 Normal[CoefficientArrays[Map[GetPolyPart, Map[DirectIneq, l]]]][[2]]
MakeAssign[v_] := v -> 0
MakeAssigns[l_] := Map[MakeAssign, l]
GenConst[p_] := -(p /. MakeAssigns[Variables[p]])
MakeEqZeroPolys[l_] := Map[Function[p, p == 0], l]
GenConsts[l_] := Map[GenConst, Map[GetPolyPart, Map[DirectIneq, l]]]
GenIneqs[l_] := Map[Head, DirectIneqs[l]]
MkVarListFor[l_] := Table[Unique["x"], Length[l]]
Unrule[Rule[_, x_]] := x
Unrules[l_] := Map[Unrule, l]
FindFalseCoeffs[l_] := 
 Module[{vs}, vs = MkVarListFor[l]; 
   FindInstance[
     Append[MakeEqZeroPolys[vs . GenCoeffMatrix[l]], 
      vs . GenConsts[l] < 0], vs][[1]]] // Unrules // ScaleList
