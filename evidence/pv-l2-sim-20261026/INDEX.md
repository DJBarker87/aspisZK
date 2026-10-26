# Lean attempts and Kani runs

Every link contains the raw output, GNU time, exact submitted source hash,
committed baseline revision and collected direct dependency object hashes.
The baseline does not describe uncommitted proof edits: the source hash does.
Dependency hashes are collected after each run, not a frozen transitive manifest.
Failed source versions are not all retained; their hashes and diagnostics are.

| Attempt | Target | Exit | Wall | Peak RSS KiB | Swap | Receipt |
|---|---|---|---|---|---|---|
| J20101 | R1Z/PV_L2_F5 | 1 | 0:01.79 | 4132524 | 0 | [receipt](J20101/receipt.json) |
| J20102 | R1Z/PV_L2_F5 | 1 | 0:01.94 | 4132176 | 0 | [receipt](J20102/receipt.json) |
| J20103 | R1Z/PV_L2_F5 | 1 | 0:02.21 | 4131288 | 0 | [receipt](J20103/receipt.json) |
| J20104 | R1Z/PV_L2_F5 | 0 | 0:02.73 | 4152252 | 0 | [receipt](J20104/receipt.json) |
| J20105 | R1Z/PV_L2_F5Transport | 1 | 0:01.85 | 4122404 | 0 | [receipt](J20105/receipt.json) |
| J20106 | R1Z/PV_L2_F5Transport | 0 | 0:01.86 | 4143260 | 0 | [receipt](J20106/receipt.json) |
| J20107 | R1Z/PV_L2_F5Absorption | 1 | 0:01.89 | 4119776 | 0 | [receipt](J20107/receipt.json) |
| J20108 | R1Z/PV_L2_F5Absorption | 0 | 0:03.08 | 4138544 | 0 | [receipt](J20108/receipt.json) |
| J20109 | R1Z/PV_L2_F3Words | 1 | 0:00.24 | 619596 | 0 | [receipt](J20109/receipt.json) |
| J20110 | R1Z/PV_L2_F3Words | 0 | 0:01.85 | 4263668 | 0 | [receipt](J20110/receipt.json) |
| J20111 | R1Z/PV_L2_F3Schedule | 1 | 0:05.73 | 4242560 | 0 | [receipt](J20111/receipt.json) |
| J20112 | R1Z/PV_L2_F3Schedule | 1 | 0:06.71 | 4246696 | 0 | [receipt](J20112/receipt.json) |
| J20113 | R1Z/PV_L2_F3Schedule | 0 | 0:07.62 | 4268660 | 0 | [receipt](J20113/receipt.json) |
| J20114 | R1Z/PV_L2_F3Adaptive | 1 | 0:05.41 | 4240968 | 0 | [receipt](J20114/receipt.json) |
| J20115 | R1Z/PV_L2_F3Adaptive | 1 | 0:06.93 | 4240488 | 0 | [receipt](J20115/receipt.json) |
| J20116 | R1Z/PV_L2_F3Adaptive | 0 | 0:04.81 | 4262728 | 0 | [receipt](J20116/receipt.json) |
| J20117 | R1Z/PV_L2_F3SeedObstruction | 1 | 0:06.95 | 4236964 | 0 | [receipt](J20117/receipt.json) |
| J20118 | R1Z/PV_L2_F3SeedObstruction | 0 | 0:05.00 | 4261076 | 0 | [receipt](J20118/receipt.json) |
| J20119 | R1Z/PV_L2_F3Recorded | 1 | 0:04.87 | 4118804 | 0 | [receipt](J20119/receipt.json) |
| J20120 | R1Z/PV_L2_F6Openings | 0 | 0:04.75 | 4206272 | 0 | [receipt](J20120/receipt.json) |
| J20121 | R1Z/PV_L2_F3Recorded | 1 | 0:05.17 | 4118836 | 0 | [receipt](J20121/receipt.json) |
| J20122 | R1Z/PV_L2_F6Sharing | 1 | 0:07.22 | 4181228 | 0 | [receipt](J20122/receipt.json) |
| J20123 | R1Z/PV_L2_F3Recorded | 0 | 0:07.18 | 4138540 | 0 | [receipt](J20123/receipt.json) |
| J20124 | R1Z/PV_L2_F6Sharing | 0 | 0:06.67 | 4204036 | 0 | [receipt](J20124/receipt.json) |
| J20125 | R1Z/PV_L2_F5Machine | 1 | 0:06.91 | 4130324 | 0 | [receipt](J20125/receipt.json) |
| J20126 | R1Z/PV_L2_F5Machine | 0 | 0:05.56 | 4151596 | 0 | [receipt](J20126/receipt.json) |
| J20127 | R1Z/PV_L2_F3WordCarrier | 1 | 0:05.24 | 4242676 | 0 | [receipt](J20127/receipt.json) |
| J20128 | R1Z/PV_L2_F3WordCarrier | 1 | 0:05.12 | 4243048 | 0 | [receipt](J20128/receipt.json) |
| J20129 | R1Z/PV_L2_F3WordCarrier | 0 | 0:05.75 | 4265408 | 0 | [receipt](J20129/receipt.json) |
| J20130 | R1Z/PV_L2_Headline | 1 | 0:11.43 | 4219456 | 0 | [receipt](J20130/receipt.json) |
| J20131 | R1Z/PV_L2_Headline | 1 | 0:17.31 | 4224472 | 0 | [receipt](J20131/receipt.json) |
| J20132 | R1Z/PV_L2_F3EntropyPrefix | 0 | 0:04.88 | 4257060 | 0 | [receipt](J20132/receipt.json) |
| J20133 | R1Z/PV_L2_Headline | 1 | 0:19.49 | 4226668 | 0 | [receipt](J20133/receipt.json) |
| J20134 | R1Z/PV_L2_Headline | 0 | 0:22.04 | 4257164 | 0 | [receipt](J20134/receipt.json) |
| J20135 | R1Z/PV_L2_Record | 1 | 0:03.10 | 2588596 | 0 | [receipt](J20135/receipt.json) |
| J20136 | R1Z/PV_L2_F3WordStream | 1 | 0:06.28 | 4236620 | 0 | [receipt](J20136/receipt.json) |
| J20137 | R1Z/PV_L2_Record | 0 | 0:04.00 | 2598592 | 0 | [receipt](J20137/receipt.json) |
| J20138 | R1Z/PV_L2_F3WordStream | 0 | 0:04.39 | 4261192 | 0 | [receipt](J20138/receipt.json) |
| J20139 | R1Z/PV_L2_F6DotStep | 1 | 0:04.41 | 2588052 | 0 | [receipt](J20139/receipt.json) |
| J20140 | R1Z/PV_L2_F6DotStep | 0 | 0:04.82 | 2594756 | 0 | [receipt](J20140/receipt.json) |
| J20141 | R1Z/PV_L2_F6Dot | 0 | 0:05.51 | 2600964 | 0 | [receipt](J20141/receipt.json) |
| J20142 | R1Z/PV_L2_F3CountedFibres | 1 | 0:09.65 | 4100760 | 0 | [receipt](J20142/receipt.json) |
| J20143 | R1Z/PV_L2_F3CountedFibres | 1 | 0:06.20 | 4109896 | 0 | [receipt](J20143/receipt.json) |
| J20144 | R1Z/PV_L2_F3CountedFibres | 1 | 0:06.56 | 4109464 | 0 | [receipt](J20144/receipt.json) |
| J20145 | R1Z/PV_L2_F3CountedFibres | 0 | 0:06.07 | 4128304 | 0 | [receipt](J20145/receipt.json) |
| J20146 | R1Z/PV_L2_F3CountedErasure | 1 | 0:06.23 | 4095944 | 0 | [receipt](J20146/receipt.json) |
| J20147 | R1Z/PV_L2_F3CountedErasure | 1 | 0:05.72 | 4096404 | 0 | [receipt](J20147/receipt.json) |
| J20148 | R1Z/PV_L2_F3CountedErasure | 1 | 0:04.96 | 4099616 | 0 | [receipt](J20148/receipt.json) |
| J20149 | R1Z/PV_L2_F6KDotStep | 0 | 0:05.55 | 2598284 | 0 | [receipt](J20149/receipt.json) |
| J20150 | R1Z/PV_L2_F3CountedErasure | 0 | 0:05.03 | 4120264 | 0 | [receipt](J20150/receipt.json) |
| J20151 | R1Z/PV_L2_F3Law | 1 | 0:05.70 | 4091268 | 0 | [receipt](J20151/receipt.json) |
| J20152 | R1Z/PV_L2_F3Law | 1 | 0:04.60 | 4096672 | 0 | [receipt](J20152/receipt.json) |
| J20153 | R1Z/PV_L2_F6KDot | 0 | 0:05.22 | 2602752 | 0 | [receipt](J20153/receipt.json) |
| J20154 | R1Z/PV_L2_F3Law | 0 | 0:05.52 | 4115900 | 0 | [receipt](J20154/receipt.json) |
| J20155 | R1Z/PV_L2_F3CountedArrays | 0 | 0:06.07 | 4119960 | 0 | [receipt](J20155/receipt.json) |
| J20156 | R1Z/PV_L2_F3Blocks | 1 | 0:16.10 | 4103656 | 0 | [receipt](J20156/receipt.json) |
| J20157 | R1Z/PV_L2_F3Blocks | 1 | 0:33.32 | 4135320 | 0 | [receipt](J20157/receipt.json) |
| J20158 | R1Z/PV_L2_F6Pivot | 1 | 0:03.08 | 2592756 | 0 | [receipt](J20158/receipt.json) |
| J20159 | R1Z/PV_L2_F3Blocks | 1 | 0:06.29 | 4107524 | 0 | [receipt](J20159/receipt.json) |
| J20160 | R1Z/PV_L2_F6Pivot | 0 | 0:04.87 | 2601812 | 0 | [receipt](J20160/receipt.json) |
| J20161 | R1Z/PV_L2_F3Blocks | 1 | 0:06.69 | 4108252 | 0 | [receipt](J20161/receipt.json) |
| J20162 | R1Z/PV_L2_F3Blocks | 0 | 0:05.98 | 4127628 | 0 | [receipt](J20162/receipt.json) |
| J20163 | R1Z/PV_L2_F3Pair | 1 | 0:06.26 | 4111752 | 0 | [receipt](J20163/receipt.json) |
| J20164 | R1Z/PV_L2_F3Pair | 0 | 0:05.49 | 4133280 | 0 | [receipt](J20164/receipt.json) |
| J20165 | R1Z/PV_L2_F3Tape | 0 | 0:04.59 | 4227140 | 0 | [receipt](J20165/receipt.json) |
| J20166 | R1Z/PV_L2_F3Disintegration | 1 | 0:04.45 | 4091316 | 0 | [receipt](J20166/receipt.json) |
| J20167 | R1Z/PV_L2_F3Disintegration | 0 | 0:05.98 | 4113388 | 0 | [receipt](J20167/receipt.json) |
| J20168 | R1Z/PV_L2_F6ImageStep | 1 | 0:04.38 | 2588208 | 0 | [receipt](J20168/receipt.json) |
| J20169 | R1Z/PV_L2_RecordBind | 0 | 0:03.68 | 2587116 | 0 | [receipt](J20169/receipt.json) |
| J20170 | R1Z/PV_L2_F3SourceCounts | 1 | 0:06.41 | 4123236 | 0 | [receipt](J20170/receipt.json) |
| J20171 | R1Z/PV_L2_F3SourceCounts | 0 | 0:06.75 | 4141088 | 0 | [receipt](J20171/receipt.json) |
| J20172 | R1Z/PV_L2_F6ImageStep | 0 | 0:01.50 | 2600324 | 0 | [receipt](J20172/receipt.json) |
| J20173 | R1Z/PV_L2_F3CompletionLaw | 0 | 0:01.85 | 4212480 | 0 | [receipt](J20173/receipt.json) |
| J20174 | R1Z/PV_L2_F3SourceArrays | 1 | 0:01.81 | 4110704 | 0 | [receipt](J20174/receipt.json) |
| J20175 | R1Z/PV_L2_F3SourceArrays | 1 | 0:02.05 | 4112136 | 0 | [receipt](J20175/receipt.json) |
| J20176 | R1Z/PV_L2_F3Absorption | 1 | 0:02.19 | 4198300 | 0 | [receipt](J20176/receipt.json) |
| J20177 | R1Z/PV_L2_F3Absorption | 1 | 0:02.19 | 4198628 | 0 | [receipt](J20177/receipt.json) |
| J20178 | R1Z/PV_L2_F3Absorption | 1 | 0:02.12 | 4201132 | 0 | [receipt](J20178/receipt.json) |
| J20179 | R1Z/PV_L2_F3Absorption | 1 | 0:01.99 | 4201448 | 0 | [receipt](J20179/receipt.json) |
| J20180 | R1Z/PV_L2_F3Absorption | 1 | 0:02.08 | 4204564 | 0 | [receipt](J20180/receipt.json) |
| J20181 | R1Z/PV_L2_F3SourceArrays | 0 | 0:01.94 | 4133932 | 0 | [receipt](J20181/receipt.json) |
| J20182 | R1Z/PV_L2_F3Absorption | 1 | 0:02.65 | 4212912 | 0 | [receipt](J20182/receipt.json) |
| J20183 | R1Z/PV_L2_F3Absorption | 1 | 0:01.95 | 4203916 | 0 | [receipt](J20183/receipt.json) |
| J20184 | R1Z/PV_L2_F6Image | 1 | 0:01.23 | 2592540 | 0 | [receipt](J20184/receipt.json) |
| J20185 | R1Z/PV_L2_F3Absorption | 1 | 0:05.69 | 4243696 | 0 | [receipt](J20185/receipt.json) |
| J20186 | R1Z/PV_L2_F6Image | 0 | 0:01.67 | 2603268 | 0 | [receipt](J20186/receipt.json) |
| J20187 | R1Z/PV_L2_F3Absorption | 1 | 0:03.51 | 4209124 | 0 | [receipt](J20187/receipt.json) |
| J20188 | R1Z/PV_L2_F3Absorption | 0 | 0:02.28 | 4265132 | 0 | [receipt](J20188/receipt.json) |
| J20189 | R1Z/PV_L2_F3SourceBudget | 1 | 0:02.21 | 4192260 | 0 | [receipt](J20189/receipt.json) |
| J20190 | R1Z/PV_L2_F3SourceBudget | 0 | 0:04.98 | 4216548 | 0 | [receipt](J20190/receipt.json) |
| J20191 | R1Z/PV_L2_F3SourceJoint | 0 | 0:01.95 | 4214920 | 0 | [receipt](J20191/receipt.json) |
| J20192 | R1Z/PV_L2_HeadlineF3 | 1 | 0:06.51 | 4224644 | 0 | [receipt](J20192/receipt.json) |
| J20193 | R1Z/PV_L2_HeadlineF3 | 0 | 0:05.90 | 4255328 | 0 | [receipt](J20193/receipt.json) |
| J20194 | R1Z/PV_L2_F3EntropyJoin | 0 | 0:02.51 | 4263636 | 0 | [receipt](J20194/receipt.json) |
| J20195 | R1Z/PV_L2_F6ProductStep | 0 | 0:01.68 | 2600108 | 0 | [receipt](J20195/receipt.json) |
| J20196 | R1Z/PV_L2_F6ProductRow | 0 | 0:01.80 | 2602656 | 0 | [receipt](J20196/receipt.json) |
| J20197 | R1Z/PV_L2_F6ProductOuterStep | 1 | 0:01.26 | 2587304 | 0 | [receipt](J20197/receipt.json) |
| J20198 | R1Z/PV_L2_F6ProductOuterStep | 0 | 0:01.40 | 2597560 | 0 | [receipt](J20198/receipt.json) |
| J20199 | R1Z/PV_L2_F6Product | 0 | 0:01.53 | 2603324 | 0 | [receipt](J20199/receipt.json) |
| J20200 | R1Z/PV_L2_Audit | 0 | 0:02.01 | 4265580 | 0 | [receipt](J20200/receipt.json) |

| Kani | Harness | Result | Exit | Wall | Peak RSS KiB | Receipt |
|---|---|---|---|---|---|---|
| k01 | F5_stop_count | passed | 0 | 0:03.66 | 284532 | [receipt](k01/receipt.json) |
| k02 | F5_stop_draws | passed | 0 | 0:04.71 | 284440 | [receipt](k02/receipt.json) |
| k03 | F5_query_words | passed | 0 | 0:04.27 | 224576 | [receipt](k03/receipt.json) |
| k04 | F5_scan_unused_suffix | timeout | 124 | 0:50.00 | None | [receipt](k04/receipt.json) |
| k05 | F5_finish_success | failed | 1 | 0:00.35 | 144804 | [receipt](k05/receipt.json) |
| k06 | F5_finish_failure | passed | 0 | 0:00.34 | 144900 | [receipt](k06/receipt.json) |
| k07 | F5_pairs_failure_advances | passed | 0 | 0:24.56 | 873900 | [receipt](k07/receipt.json) |
| k08 | F5_gamma_add | passed | 0 | 0:01.46 | 162084 | [receipt](k08/receipt.json) |
| k09 | F5_div_pass | timeout | 124 | 0:50.00 | None | [receipt](k09/receipt.json) |
| k10 | F6_well_formed | passed | 0 | 0:47.33 | 2102384 | [receipt](k10/receipt.json) |
| k11 | F6_single_binary | timeout | 124 | 0:50.00 | None | [receipt](k11/receipt.json) |
| k12 | F6_single_eight | timeout | 124 | 0:50.00 | None | [receipt](k12/receipt.json) |
| k13 | F6_pair_binary | timeout | 124 | 0:50.00 | None | [receipt](k13/receipt.json) |
| k14 | F6_arbitrary_binary | timeout | 124 | 0:50.00 | None | [receipt](k14/receipt.json) |
| k15 | F6_bad_empty | passed | 0 | 0:05.15 | 273188 | [receipt](k15/receipt.json) |
| k16 | F6_bad_range | timeout | 124 | 0:50.01 | None | [receipt](k16/receipt.json) |
| k17 | F6_bad_order | timeout | 124 | 0:50.00 | None | [receipt](k17/receipt.json) |
| k18 | F5_gamma_zero | passed | 0 | 0:01.74 | 152084 | [receipt](k18/receipt.json) |
| k19 | F5_gamma_wrap | passed | 0 | 0:01.45 | 152256 | [receipt](k19/receipt.json) |
| k20 | F5_div_zero | passed | 0 | 0:01.09 | 145108 | [receipt](k20/receipt.json) |
