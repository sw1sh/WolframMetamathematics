Package["Wolfram`Metamathematics`"]

PackageExport["universalPatterns"]
PackageExport["skolemPatterns"]
PackageExport["unquantifyFormula"]
PackageExport["rulifyFormula"]
PackageExport["rulifyLiteral"]



universalPatterns[expr_ /; ! FreeQ[expr, _ForAll], bound_ : {}] := expr //. HoldPattern[ForAll[var_, cond___, subExpr_]] :> With[{vars = Replace[var, v : Except[_List] :> {v}]},
	With[{repl = Block[{$ModuleNumber = 1}, Thread[vars -> Unique /@ vars]]},
		With[{patternRepl = MapAt[Pattern[#, Blank[]] &, repl, {All, 2}]},
			With[{res = skolemPatterns[subExpr, Join[vars, bound]] /. patternRepl},
				If[ Length[{cond}] > 0,
					With[{newCond = cond /. repl}, res /; newCond],
					res
				]
			]
		]
	]
]
universalPatterns[expr_, ___] := expr


skolemPatterns[expr_ /; ! FreeQ[expr, _Exists], bound_ : {}] := expr //. HoldPattern[Exists[var_, cond___, subExpr_]] :> With[{vars = Replace[var, v : Except[_List] :> {v}]},
	With[{repl = Block[{$ModuleNumber = 1}, Thread[vars -> (If[Length[bound] > 0, Unique[#] @@ bound, Unique[#]] & /@ vars)]]},
		If[ Length[{cond}] > 0,
			universalPatterns[subExpr, bound] && cond /. repl,
			universalPatterns[subExpr, bound] /. repl
		]
	]
]
skolemPatterns[expr_, ___] := expr


unquantifyFormula[expr_] := expr /. {universal_ForAll :> universalPatterns[universal], existential_Exists :> skolemPatterns[existential]}


rulifyFormula[expr_] := BooleanConvert[unquantifyFormula[expr /. ex_Exists \[Implies] rhs_ :> Not[ex] || rhs], "CNF"] //
	Replace[{and_And :> List @@ and, x_ :> {x}}] //
	ReplaceAll[or_Or :> Splice @ Permutations[or]] //
	Map[BooleanConvert[#, "IMPLIES"] &] //
	ReplaceAll[{Implies -> Rule, Equivalent | Equal -> TwoWayRule(* And -> List, Not -> Except , Or -> Alternatives*)(*, True -> Nothing, False -> Sequence[]*)}] //
	Flatten //
	Map[canonicalizePatterns] //
    rulifyLiteral


rulifyLiteral[expr : Except[_List]] :=
	Replace[expr, {
		formula : _Rule | _TwoWayRule :> {formula},
		formula : Except[_Rule | _TwoWayRule] :> {formula <-> True, Not[formula] <-> False, False -> formula}}]

rulifyLiteral[expr_List] := Splice @* rulifyLiteral /@ expr

