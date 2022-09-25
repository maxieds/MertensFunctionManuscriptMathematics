
(*************************************************************************)
(*************************************************************************)
(********************* : ComputePrimeCerts.m:         ********************) 
(*************************************************************************)
(*************************************************************************)

BeginPackage["ComputePrimeCerts`"]

(**** : Clear out any old definitions and stored data on reload: ****)
Clear[CheckIndicatorSumBound, GetPrimeLists, RemoveSelectedPrimes]

(**** : Our parity function of interest defined for convenience : ****)
Nex[x_] := Sum[If[Mod[PartitionsP[n], 2, 0] == 0, 1, 0], {n, 1, x}]

(**** : Utilities for computing primes in intervals : ****)
PrimeIn[lower_, upper_] := Select[Table[Prime[m], {m, 1, upper}], 
                                  # >= Ceiling[lower] && # <= Floor[upper] &]
s[t_, eps_] := PrimeIn[t^(2/(1 + 2*eps)), (t + 1)^(2/(1 + 2*eps))]

GetPrimeDifferenceSet[Qx_] := 
     Module[{diffs, s, i}, 
     
     diffs = {}; 
     For[s = 1, s <= Length[Qx], s++,
          For[i = s + 1, i <= Length[Qx], i++,
               diffs = Append[diffs, Qx[[i]] - Qx[[s]]];
          ];
     ];
     Return[diffs];

];

PrimeSelectWeightMetric[pdiffs_] := 
     Module[{dmax, modfns, resfns, indsum, indi, resfn, modfn, 
     
     moddiffset, numind1, j},
     dmax = Max[pdiffs];
     modfns = {12 # &, (12 # + 2) &, (72 # - 2) &, (72 # + 26) &};
     resfns = {# &, 0 &, -2 + # (73 + 3 #) &, (26 + #) (1 + 3 #) &};
     indsum = 0;
     For[indi = 1, indi <= 4, indi++,
          {resfn, modfn} = {resfns[[indi]], modfns[[indi]]};
          For[j = 1, j <= dmax, j++,
               moddiffset = Tally[Mod[pdiffs, modfn[j], 0]];
               numind1 = Plus @@ Map[#1[[2]] &, Select[moddiffset, #[[1]] == resfn[j] &]];
               indsum += numind1;
          ];
     ];
     Return[indsum];

];

PIntSelectFn[lst_, lastprimes_] := 
     Module[{weights},
   
     If[Length[lastprimes] == 0,(* select the smallest possible choice *)
          Return[Min[lst]];
     ];
     weights = Map[{#1, PrimeSelectWeightMetric[#1 - lastprimes]} &, lst];
     weights = SortBy[weights, #[[2]] &];
     Return[weights[[1]][[1]]];
   
];

GetPrimeLists[t_, eps_] := GetPrimeLists[t, eps] = 
     Module[{pints, r},
   
     If[t == 1, 
          Return[{2}]; 
     ]; 
     pints = GetPrimeLists[t-1, eps];
     pints = Append[pints, PIntSelectFn[s[t, eps], pints]];
     Return[pints];

];

RemoveSelectedPrimes[t_, eps_, ratiofn_] := RemoveSelectedPrimes[t, eps, ratiofn] = 
     Module[{initplist, nextlstsize, modplist, e, nextprime},
   
     initplist = GetPrimeLists[t, eps];
     nextlstsize = Ceiling[Length[initplist]/ratiofn[Power[t+1, (2/(1+2*eps))^2]]];
     modplist = {};
     For[e = 1, e <= nextlstsize, e++,
          nextprime = PIntSelectFn[initplist, modplist];
          modplist = Append[modplist, nextprime];
          initplist = Select[initplist, # != nextprime &];
     ];
     Return[modplist];
   
];

PrimeListChooser[t_, eps_, ratiofn_] := 
     Module[{}, 
     
     If[ratiofn == Null, 
          Return[GetPrimeLists[t, eps]];
     ];
     Return[RemoveSelectedPrimes[t, eps, ratiofn]];
     
]; 

CheckIndicatorSumBound::usage = "TODO"
CheckIndicatorSumBound[t_, eps_:0.01, ratiofn_:Null] := 
     CheckIndicatorSumBound[x, eps, ratiofn] = 
     Module[{primes, pdiffs, dmax, modfns, resfns, indsum, indi, resfn, modfn, j, moddiffset, numind1},
    
     primes = PrimeListChooser[t, eps, ratiofn];
     pdiffs = Sort[GetPrimeDifferenceSet[primes]];
     dmax = Max[pdiffs];
     modfns = {12 # &, (12 # + 2) &, (72 # - 2) &, (72 # + 26) &};
     resfns = {# &, 0 &, -2 + # (73 + 3 #) &, (26 + #) (1 + 3 #) &};
     indsum = 0;
     For[indi = 1, indi <= 4, indi++,
          {resfn, modfn} = {resfns[[indi]], modfns[[indi]]};
          For[j = 1, j <= dmax, j++,
               moddiffset = Tally[Mod[pdiffs, modfn[j], 0]];
               numind1 = Plus @@ Map[#1[[2]] &, Select[moddiffset, #[[1]] == resfn[j] &]];
               indsum += numind1;
          ];
     ];
     Return[indsum];
    
];




(*************************************************************************)
(**** : Perform pretty printing of the package details and          : ****) 
(**** : revsision information if the package is loaded in a notebook: ****)
(*************************************************************************)
packageAnnouncementStrs = 
     {Style["ComputePrimeCerts.m Package (2017.10.11-v1) Loaded ... \n\n", Bold, Underlined, Larger], 
     Style["\[RightArrowBar] Author: Maxie D. Schmidt (maxieds@gmail.com)\n", Italic, Purple], 
     Style["\[RightArrowBar] Typical Usage: " <> 
           "Table[{Index->t, ApproxX->Ceiling[(t+1)^(1.96/0.51)], CheckIndicatorSumBound[t, 0.01, Log[#]&]}, {t, 1, 50}] // TableForm\n", 
           Italic, Purple]};
packageAnnouncementStrs = Apply[StringJoin, ToString[#, StandardForm] & /@ ComputePrimeCerts`packageAnnouncementStrs]; 

If[$Notebooks,
     CellPrint[Cell[packageAnnouncementStrs, "Print", 
                    FontColor -> RGBColor[0, 0, 0], 
                    FontSize -> 12, 
                    CellFrame -> 0.5, 
                    CellFrameColor -> Purple, 
                    Background -> LightGreen, 
                    CellFrameMargins -> 14
                   ]
              ],
     Print[packageAnnouncementStrs]; 
]; 

EndPackage[]

(*************************************************************************)
(*************************************************************************)
(*************************************************************************)
(*************************************************************************)
