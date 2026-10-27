# Resumed Lean receipts, allocation 6

Caps: Lean -M7000, MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64; one capped scope at a time. All raw output, timings, exact source/input hashes and complete printed axioms/errors remain in resume6-attempts.jsonl and out/time/sha-ID files. Kernel success is distinct from the standard-axiom/profile validation.

| ID | Exact target | Kernel exit | Validation | Wall | Peak RSS KiB | Swap | Source revision | Axiom reports |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 37102 | R1NaturalProjection | 1 | REJECTED sorryAx | 0:01.41 | 2729920 | 0 | 79e2278e2e | 8/8 |
| 37103 | R1Z/PV_Src_DynamicCallEquation | 0 | standard | 0:01.64 | 4103936 | 0 | 481f6f8b43 | 2/2 |
| 37104 | R1Z/PV_Src_PureCallEquation | 0 | standard | 0:02.04 | 4096368 | 0 | 481f6f8b43 | 1/1 |
| 37105 | R1Z/PV_Src_ProjectionProofs | 1 | REJECTED compile/report | 0:00.17 | 465756 | 0 | ff6a78f442 | 0/8 |
| 37106 | R1Z/PV_Src_RootRecurrence | 0 | standard | 0:01.92 | 4116808 | 0 | ff6a78f442 | 1/1 |
| 37107 | R1Z/PV_Src_ProjectionProofs | 0 | standard | 0:01.67 | 2743320 | 0 | ff6a78f442 | 8/8 |
| 37108 | R1Z/PV_Src_RootSourceEquation | 0 | standard | 0:01.71 | 4109036 | 0 | ff6a78f442 | 2/2 |
| 37109 | R1Z/PV_Src_RootPrefix | 1 | REJECTED compile/report | 0:01.54 | 4083720 | 0 | ff6a78f442 | 1/2 |
| 37110 | R1Z/PV_Src_RootPrefix | 0 | standard | 0:01.69 | 4105740 | 0 | ff6a78f442 | 2/2 |
| 37111 | R1Z/PV_Src_RootCertificate | 1 | REJECTED sorryAx | 0:01.66 | 4089300 | 0 | ff6a78f442 | 2/2 |
| 37112 | R1Z/PV_Src_RootCertificate | 0 | standard | 0:01.68 | 4110696 | 0 | ff6a78f442 | 2/2 |
| 37113 | R1Z/PV_Src_PortReduce | 1 | REJECTED sorryAx | 0:01.70 | 4118420 | 0 | ff6a78f442 | 2/2 |
| 37114 | R1Z/PV_Src_PortReduce | 0 | standard | 0:01.63 | 4143704 | 0 | ff6a78f442 | 2/2 |
| 37116 | R1Z/PV_Src_PortMultiply | 0 | standard | 0:01.61 | 4136484 | 0 | c3de513796 | 2/2 |
| 37117 | R1Z/PV_Src_PortAddition | 0 | standard | 0:01.70 | 4127484 | 0 | c3de513796 | 2/2 |
| 37118 | AeneasMeta/Extensions | 0 | standard | 0:00.61 | 1577528 | 0 | c3de513796 | 0/0 |
| 37119 | Aeneas/Extract/Extract | 0 | standard | 0:03.80 | 1708316 | 0 | c3de513796 | 0/0 |
| 37120 | Aeneas/Extract | 0 | standard | 0:00.59 | 1566368 | 0 | c3de513796 | 0/0 |
| 37121 | Aeneas/Std/Primitives | 0 | standard | 0:01.08 | 1613500 | 0 | c3de513796 | 0/0 |
| 37122 | Aeneas/Std/Core/Core | 0 | standard | 0:00.71 | 1618696 | 0 | c3de513796 | 0/0 |
| 37123 | Aeneas/Std/Scalar/Core | 0 | standard | 0:12.46 | 2353548 | 0 | c3de513796 | 0/0 |
| 37124 | Aeneas/Tactic/Solver/ScalarTac | 0 | standard | 0:01.14 | 2540552 | 0 | c3de513796 | 0/0 |
| 37127 | Aeneas/Std/Scalar/Notations | 0 | standard | 0:02.11 | 2583692 | 0 | c3de513796 | 0/0 |
| 37128 | Aeneas/Data/Discriminant | 0 | standard | 0:04.11 | 2588852 | 0 | c3de513796 | 0/0 |
| 37130 | Aeneas/Data | 0 | standard | 0:01.09 | 2559524 | 0 | c3de513796 | 0/0 |
| 37132 | Aeneas/Std/Array/Array | 0 | standard | 0:02.97 | 2604588 | 0 | c3de513796 | 0/0 |
| 37134 | Aeneas/Std/Core/Result | 0 | standard | 0:00.62 | 1578168 | 0 | c3de513796 | 0/0 |
| 37135 | Aeneas/Std/Core/Convert | 0 | standard | 0:00.78 | 1618808 | 0 | c3de513796 | 0/0 |
| 37136 | Aeneas/Std/Core/Fmt | 0 | REJECTED profile | 0:01.38 | 2580860 | 0 | c3de513796 | 0/0 |
| 37137 | Aeneas/Std/Core/Discriminant | 0 | standard | 0:01.13 | 2567484 | 0 | c3de513796 | 0/0 |
| 37138 | Aeneas/Std/Core/Iter | 0 | standard | 0:03.12 | 2673180 | 0 | c3de513796 | 0/0 |
| 37139 | Aeneas/Std/RawPtr | 0 | standard | 0:00.97 | 2142020 | 0 | c3de513796 | 0/0 |
| 37140 | Aeneas/Std/Core/Ptr | 0 | standard | 0:01.21 | 2145952 | 0 | c3de513796 | 0/0 |
| 37141 | Aeneas/Std/Slice | 0 | standard | 0:12.33 | 2681028 | 0 | c3de513796 | 0/0 |
| 37142 | Aeneas/Std/SliceIter | 0 | standard | 0:02.09 | 2615868 | 0 | c3de513796 | 0/0 |
| 37143 | Aeneas/Std/RangeIter | 0 | standard | 0:05.26 | 2669740 | 0 | c3de513796 | 0/0 |
| 37145 | Aeneas/Tactic | 0 | standard | 0:01.03 | 2602824 | 0 | c3de513796 | 0/0 |
| 37146 | AspisV8R19/SamplerWordRead | 0 | REJECTED core.fmt.Formatter | 0:01.98 | 3826064 | 0 | c3de513796 | 8/8 |
| 37147 | Mathlib/Algebra/Polynomial/BigOperators | 0 | standard | 0:02.44 | 1118112 | 0 | c3de513796 | 0/0 |
| 37148 | Mathlib/Algebra/Polynomial/Degree/Defs | 0 | standard | 0:02.27 | 1069940 | 0 | c3de513796 | 0/0 |
| 37149 | Mathlib/Algebra/Polynomial/Degree/Operations | 0 | standard | 0:03.29 | 1134576 | 0 | c3de513796 | 0/0 |
| 37150 | Mathlib/Algebra/Polynomial/Eval/Defs | 0 | standard | 0:02.89 | 1073416 | 0 | c3de513796 | 0/0 |
| 37151 | Mathlib/Data/ZMod/Basic | 0 | standard | 0:04.38 | 1085200 | 0 | c3de513796 | 0/0 |
| 37152 | Mathlib/Tactic/Ring | 0 | standard | 0:00.46 | 890652 | 0 | c3de513796 | 0/0 |
| 37199 | R1Z/PV_Src_Transport | 0 | standard | 0:01.61 | 4102660 | 0 | c3de513796 | 5/5 |
| 37200 | R1Z/PV_Src_NativePremises | 0 | standard | 0:01.59 | 4110752 | 0 | c3de513796 | 1/1 |
| 37203 | R1Z/ProverCommitCallerInstance | 0 | standard | 0:02.44 | 4137736 | 0 | c3de513796 | 6/6 |
| 37204 | R1Z/ProverCommitSectionObstruction | 0 | standard | 0:01.50 | 3586788 | 0 | c3de513796 | 2/2 |
| 37205 | Aeneas/Std/Core/Fmt | 0 | standard | 0:01.14 | 2581044 | 0 | c3de513796 | 0/0 |
| 37206 | R1Z/PV_Src_FormatterAudit | 0 | standard | 0:00.96 | 2550380 | 0 | c3de513796 | 1/1 |
| 37207 | R1Z/PV_Src_PortField | 0 | standard | 0:01.71 | 4143052 | 0 | c3de513796 | 3/3 |
| 37208 | R1Z/PV_Src_PortSboxStep | 0 | standard | 0:01.69 | 4147972 | 0 | c3de513796 | 3/3 |
| 37209 | R1Z/PV_Src_FormatterAudit | 0 | standard | 0:01.03 | 2551484 | 0 | c3de513796 | 2/2 |
| 37210 | R1Z/PV_Src_PortSboxLoop | 0 | standard | 0:02.01 | 4150228 | 0 | c3de513796 | 2/2 |
| 37211 | R1Z/PV_Src_CacheInventory | 0 | standard | 0:01.69 | 4263152 | 0 | c3de513796 | 0/0 |
| 37212 | R1Z/PV_Src_PortTables | 0 | standard | 0:01.12 | 2594104 | 0 | c3de513796 | 3/3 |
| 37213 | Aeneas/Std/Array/ArraySlice | 0 | standard | 0:03.06 | 2617284 | 0 | c3de513796 | 0/0 |
| 37214 | Aeneas/Std/Array | 0 | standard | 0:00.92 | 2550872 | 0 | c3de513796 | 0/0 |
| 37215 | Aeneas/Std/Core | 0 | standard | 0:00.93 | 2573660 | 0 | c3de513796 | 0/0 |
| 37216 | Aeneas/Std | 0 | standard | 0:00.93 | 2577820 | 0 | c3de513796 | 0/0 |
| 37217 | Aeneas | 0 | standard | 0:01.01 | 2604496 | 0 | c3de513796 | 0/0 |
| 37218 | ImportUnionNamedDiscriminant | 0 | standard | 0:01.08 | 2633820 | 0 | c3de513796 | 0/0 |
| 37219 | R1Z/BuilderAdmissionStd | 0 | standard | 0:01.45 | 2604580 | 0 | c3de513796 | 3/3 |
| 37220 | R1Z/BuilderAdmissionExtracted | 0 | standard | 0:01.84 | 2684264 | 0 | c3de513796 | 1/1 |
| 37221 | R1Z/BuilderRecordsExtracted | 0 | standard | 0:01.68 | 2629124 | 0 | c3de513796 | 0/0 |
| 37222 | R1Z/BuilderRecordsFields | 0 | standard | 0:00.99 | 2593384 | 0 | c3de513796 | 2/2 |
| 37223 | R1Z/BuilderAdmissionRanges | 0 | standard | 0:01.10 | 2630496 | 0 | c3de513796 | 4/4 |
| 37224 | R0P/Core | 0 | standard | 0:01.24 | 3309764 | 0 | c3de513796 | 0/0 |
| 37225 | R0P/CoreExt | 0 | standard | 0:01.31 | 3307684 | 0 | c3de513796 | 1/1 |
| 37226 | AspisFormal/V5ComponentCConcreteFoldLinearity | 0 | standard | 0:02.77 | 2016720 | 0 | c3de513796 | 17/17 |
| 37227 | AspisFormal/V5FriListCap | 0 | standard | 0:03.78 | 2571012 | 0 | c3de513796 | 7/7 |
| 37228 | AspisFormal/CircleFibreRoots | 0 | standard | 0:02.41 | 2060796 | 0 | c3de513796 | 6/6 |
| 37229 | AspisFormal/CircleGroupOrder | 0 | standard | 0:03.41 | 2383484 | 0 | c3de513796 | 4/4 |
| 37230 | AspisFormal/SoundnessLedger | 0 | standard | 0:03.72 | 2676000 | 0 | c3de513796 | 14/14 |
| 37231 | AspisFormal/V5WithoutReplacementQuerySoundness | 0 | standard | 0:01.46 | 2654332 | 0 | c3de513796 | 9/9 |
| 37232 | AspisFormal/V5FriCoherentCandidateExtraction | 0 | standard | 0:02.97 | 2697716 | 0 | c3de513796 | 9/9 |
| 37233 | AspisFormal/V5FriConcreteEncoderCommutation | 0 | standard | 0:05.22 | 2728508 | 0 | c3de513796 | 15/15 |
| 37234 | AspisFormal/V5FriJohnsonListBound | 0 | standard | 0:07.31 | 1959008 | 0 | c3de513796 | 7/7 |
| 37235 | AspisFormal/V6OneFoldParameterAudit | 0 | standard | 0:02.18 | 2692888 | 0 | c3de513796 | 13/13 |
| 37236 | AspisFormal/CircleNaturalBasisEval | 0 | standard | 0:00.93 | 2178016 | 0 | c3de513796 | 0/0 |
| 37237 | AspisFormal/CircleNaturalBasis | 0 | standard | 0:01.10 | 2293568 | 0 | c3de513796 | 0/0 |
| 37238 | AspisFormal/V5FunctionalBatching | 0 | standard | 0:01.45 | 2658516 | 0 | c3de513796 | 6/6 |
| 37239 | AspisFormal/V5FriInitialListBound | 0 | standard | 0:01.30 | 2663580 | 0 | c3de513796 | 10/10 |
| 37240 | AspisFormal/V5FriNaturalBasisRadix4 | 0 | standard | 0:01.11 | 2183972 | 0 | c3de513796 | 1/1 |
| 37241 | AspisFormal/V5FriConcreteEncoderApplicability | 0 | standard | 0:03.82 | 2792960 | 0 | c3de513796 | 21/21 |
| 37242 | AspisFormal/V6Width29CorrelatedAgreement | 0 | standard | 0:01.68 | 2751672 | 0 | c3de513796 | 4/4 |
| 37245 | AspisFormal/V5FriDegreeThreeCorrelatedAgreement | 0 | standard | 0:01.39 | 2663676 | 0 | 888aa93f5e | 6/6 |
| 37246 | AspisFormal/CircleGroupCardinality | 0 | standard | 0:01.17 | 2222596 | 0 | 888aa93f5e | 2/2 |
| 37251 | AspisFormal/V5FriCircleEncoderDistance | 0 | standard | 0:05.67 | 2693528 | 0 | 888aa93f5e | 7/7 |
| 37252 | AspisFormal/V6OneFoldCandidateExtraction | 0 | standard | 0:02.96 | 2671776 | 0 | 888aa93f5e | 5/5 |
| 37253 | AspisFormal/V6EncoderDistance | 0 | standard | 0:01.55 | 2749796 | 0 | 888aa93f5e | 7/7 |
| 37254 | AspisFormal/V6PublishedTheoremInterfaces | 0 | standard | 0:01.66 | 2746320 | 0 | 888aa93f5e | 8/8 |
| 37255 | AspisFormal/Pool/AlgorithmicCircleDecoderV7 | 0 | standard | 0:01.59 | 2753892 | 0 | 888aa93f5e | 16/16 |
| 37256 | AspisFormal/V5FriBitReverse | 0 | standard | 0:01.38 | 1667840 | 0 | 888aa93f5e | 4/4 |
| 37257 | AspisFormal/V5FriExactLineDomains | 0 | standard | 0:02.16 | 2226860 | 0 | 888aa93f5e | 7/7 |
| 37258 | AspisFormal/V5FriInitialCircleEncoderIdentity | 0 | standard | 0:11.51 | 2894304 | 0 | 888aa93f5e | 4/4 |
| 37260 | R1NaturalProjection | 1 | REJECTED sorryAx | 0:01.58 | 2728704 | 0 | 888aa93f5e | 8/8 |
| 37263 | R1Z/PV_Src_FinalAudit6A | 0 | standard | 0:01.80 | 4234508 | 0 | 888aa93f5e | 206/206 |
| 37264 | R1Z/PV_Src_FinalAudit6B | 0 | standard | 0:01.83 | 4234568 | 0 | 888aa93f5e | 205/205 |
| 37265 | R1Z/PV_Src_FinalAudit6C | 0 | standard | 0:02.01 | 4266752 | 0 | 888aa93f5e | 205/205 |
