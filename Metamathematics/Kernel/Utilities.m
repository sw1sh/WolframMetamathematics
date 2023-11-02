Package["Wolfram`Metamathematics`"]

PackageImport["GeneralUtilities`"]


PackageExport["wrap"]
PackageExport["rests"]
PackageExport["mosts"]
PackageExport["extract"]
PackageExport["replacePart"]
PackageExport["mapAt"]
PackageExport["replaceAllUnderHold"]
PackageExport["MapAtInplace"]
PackageExport["uniquifyPatterns"]
PackageExport["CanonicalizePatterns"]
PackageExport["formalizePatterns"]
PackageExport["makeReplaceRule"]
PackageExport["makePatternRule"]
PackageExport["PatternsToSymbols"]
PackageExport["SymbolsToPatterns"]
PackageExport["DependentWith"]
PackageExport["TuplePosition"]
PackageExport["OrderedTuplePosition"]
PackageExport["OrderedTuples"]
PackageExport["subsetPosition"]
PackageExport["HoldOuter"]
PackageExport["HoldApply"]
PackageExport["FirstAt"]
PackageExport["BeheadAt"]


wrap[expr_, head_ : List] := Replace[expr, x : Except[_head] :> head[x]]


rests[l_List] := NestList[Rest, l, Length @ l]


mosts[l_List] := NestList[Most, l, Length @ l]


extract[expr_, pos : {_Integer ...}, f_] :=  If[pos === {}, f @ expr, Enclose[
    ConfirmQuiet[Extract[Unevaluated @ expr, pos, f], {Extract::partd, Extract::partw}],
    Missing[ReleaseHold @ #["HeldMessageName"]] &]
]

extract[expr_, pos : {_Integer ...}] :=  If[pos === {}, expr, Enclose[
    ConfirmQuiet[Extract[Unevaluated @ expr, pos], {Extract::partd, Extract::partw}],
    Missing[ReleaseHold @ #["HeldMessageName"]] &]
]


replacePart[expr_, pos : {_Integer ...} -> part_] := If[pos === {}, part, ReplacePart[expr, pos -> part]]

replacePart[expr_, rules_List] := ReplacePart[expr, MapAt[Replace[{} -> {{}}], {1}] /@ rules]


mapAt[f_, expr_, pos_] := If[pos === {}, f @ expr, MapAt[f, expr, pos]]

mapAt[f_, pos_][expr_] := mapAt[f, expr, pos]


Options[replaceAllUnderHold] := Options[Position];

replaceAllUnderHold[expr_, rule_ ? RuleQ, opts : OptionsPattern[]] := replaceAllUnderHold[expr, {rule}, opts]

replaceAllUnderHold[expr_, rules : {_ ? RuleQ...}, opts : OptionsPattern[]] := With[{
    pos = Position[Unevaluated[expr], Alternatives @@ rules[[All, 1]], opts]
},
    With[{rhs = Unevaluated @@@ Replace[Extract[Unevaluated[expr], pos, Hold], MapAt[RuleCondition, rules, {All, 2}], {2}]},
        replacePart[Unevaluated[expr], Thread[pos :> rhs]]
    ]
]

replaceAllUnderHold[rules_, opts : OptionsPattern[]][expr_]:= replaceAllUnderHold[expr, rules, opts]


MapAtInplace[f_, expr_, pos_List] := Fold[ReplacePart[#1, Sequence @@ #2] &, expr, Thread[{Extract[expr, pos, f], pos}]]

MapAtInplace[f_, expr_, pos : {_Integer...}] := ReplacePart[expr, Extract[expr, pos, f], pos]

MapAtInplace[f_, pos_][expr_] := MapAtInplace[f, expr, pos]


uniquifyPatterns[expr_] := ReplaceAll[expr,
    Union @ Cases[expr, x_Pattern, All, Heads -> True] /.
    x_Pattern :> Verbatim[x] -> Pattern @@ {Unique[Symbol @ First @ StringSplit[SymbolName @ First @ x, "$"]], Last @ x}
]

uniquifyPatterns[expr1_, expr2_] := ReplaceAll[expr1,
    Intersection[Cases[expr1, _Pattern, All, Heads -> True], Cases[expr2, _Pattern, All, Heads -> True]] /.
    x_Pattern :> Verbatim[x] -> Pattern @@ {Unique[Symbol @ First @ StringSplit[SymbolName @ First @ x, "$"]], Last @ x}
]


Options[CanonicalizePatterns] := {"SymbolNames" -> "Alphabet"}

CanonicalizePatterns[expr_, OptionsPattern[]] := Module[{
    chars = Replace[
        OptionValue["SymbolNames"],
        {
            Automatic -> Join[CharacterRange["\[FormalA]", "\[FormalZ]"], CharacterRange["\[FormalCapitalA]", "\[FormalCapitalZ]"]],
            "Alphabet" | Alphabet -> Alphabet[]
        }
    ],
    patts = DeleteDuplicates @ Cases[expr, _Pattern, All, Heads -> True]
},
    chars = First @ NestWhile[Apply[{cs, n} |-> {Join[cs,  (# <> ToString[n]) & /@ cs], n + 1}], {chars, 1}, Length[#[[1]]] < Length[patts] &];
    ReplaceAll[expr,
        MapIndexed[
            With[{canonical = Pattern @@ {
                    Symbol @ Extract[
                        chars,
                        #2
                    ],
                    Last @ #1
                }},
                Verbatim[#1] :> canonical
            ] &,
            patts
        ]
    ]
]

CanonicalizePatterns[expr1_, expr2_] := ReplaceAll[expr1,
    MapIndexed[
        With[{canonical = Pattern @@ {Symbol @ Extract[Alphabet[], #2], Last @ #1}}, Verbatim[#1] :> canonical] &,
        Intersection[Cases[expr1, _Pattern, All, Heads -> True], Cases[expr2, _Pattern, All, Heads -> True]]
    ]
]


formalizePatterns[expr_] := replaceAllUnderHold[expr, Verbatim[Pattern][name_Symbol, obj_] :> Pattern @@ {ResourceFunction["FormalizeSymbols"][name], obj}]


SetAttributes[makeReplaceRule, HoldRest]
makeReplaceRule[lhs_, rhs_] := With[{newRHS = ReplaceAll[Hold[rhs], (Verbatim[#] -> First[#] & /@ DeleteDuplicates @ Cases[lhs, _Pattern, All, Heads -> True])]},
    ReleaseHold[RuleDelayed @@ {lhs, newRHS}]
]


SetAttributes[makePatternRule, HoldRest]
makePatternRule[lhs_, rhs_] := With[{newRHS = ReplaceAll[Hold[rhs], (First[#] -> # & /@ DeleteDuplicates @ Cases[lhs, _Pattern, All, Heads -> True])]},
    ReleaseHold[RuleDelayed @@ {lhs, newRHS}]
]


PatternsToSymbols[expr_] := replaceAllUnderHold[expr, p_Pattern :> First[p]]

PatternsToSymbols[g_Graph] := VertexReplace[g, v_ :> PatternsToSymbols[v]]


SymbolsToPatterns[expr_, prefix : {_String..} : {"x", "y", "z"}] :=
    expr /. x_Symbol /; StringMatchQ[SymbolName[x], Alternatives @@ prefix ~~ DigitCharacter...] :> Pattern @@ {x, _}

SymbolsToPatterns[expr_, prefix : {_Symbol..}] := SymbolsToPatterns[expr, SymbolName /@ prefix]


DependentWith // Attributes = {HoldAll}
DependentWith[{x_, xs___}, expr_] := With[{x}, DependentWith[{xs}, expr]]
DependentWith[{}, expr_] := expr


TuplePosition[expr : _List | _Association, patt_List] := If[AssociationQ[expr], ReplaceAll[{Key[k_]} :> k], Identity] @
      Select[Tuples[Position[expr, #, {1}, Heads -> False] & /@ patt], MatchQ[Extract[expr, #], patt] &]

subsetPosition[expr : _List | _Association, patt_List] := If[AssociationQ[expr],
    Part[Keys[expr], #] & /@ SubsetPosition[Values @ expr, patt],
      Map[List, SubsetPosition[expr, patt], {2}]
]

OrderedTuplePosition[expr : _List | _Association, patt_List] := If[AssociationQ[expr], ReplaceAll[{Key[k_]} :> k], Identity] @
    Select[DeleteDuplicatesBy[Tuples[Position[expr, #, {1}, Heads -> False] & /@ patt], Sort], MatchQ[Extract[expr, #], patt] &]

OrderedTuples[list_List, n_Integer] := DeleteDuplicatesBy[Tuples[list, n], Sort]


releaseInnerHold[expr_] := With[{pos = FirstPosition[expr, _Hold | _HoldForm]},
    If[ MissingQ[pos] || pos === {0},
        expr,
        ReplacePart[expr,
            With[{e = Unevaluated @@ Extract[expr, pos]}, pos :> e]]
        ]
    ]

HoldOuter[expr : (Hold | HoldForm)[_]] := FixedPoint[releaseInnerHold, expr]

HoldOuter[expr_] := HoldOuter[HoldForm[expr]]


HoldApply[f_] := Function[Null, f @@ Unevaluated @ #, HoldAll]


FirstAt[expr_, pos : {_Integer...}] := With[{r = extract[expr, pos, Function[Null, Sequence @@ Unevaluated @ #, HoldFirst]]},
	ReplacePart[expr, Replace[pos, {} -> {{}}] :> r]
]
FirstAt[expr_, pos : {{_Integer...}...}] := Fold[FirstAt, Unevaluated @ expr, pos]
FirstAt[pos_][expr_] := FirstAt[Unevaluated @ expr, pos]


BeheadAt[expr_, p_Integer] := BeheadAt[Unevaluated @ expr, {p}]
BeheadAt[expr_, {}] := Sequence @@ expr
BeheadAt[expr_, pos : {___, 0}] := ReplacePart[expr, Append[pos, 0] -> Sequence]
BeheadAt[expr_, pos : {_Integer..}] := With[{
	head = Unevaluated @@ Extract[Unevaluated @ expr, Append[Most @ pos, 0], Hold]
},
	With[{
		r = ReplacePart[extract[Unevaluated @ expr, Most @ pos, HoldApply[Hold]], {Last[pos], 0} -> Sequence]
	},
		With[{beheaded = Unevaluated @@ ReplacePart[Hold @ expr, Prepend[Most @ pos, 1] :> r]},
			ReplacePart[beheaded, Append[Most @ pos, 0] :> head]
		]
	]
]
BeheadAt[expr_, pos : {{_Integer...}...}] := Fold[Function[Null, BeheadAt[Unevaluated[#1], #2], HoldFirst], Unevaluated @ expr, pos]
BeheadAt[pos_][expr_] := BeheadAt[Unevaluated @ expr, pos]

