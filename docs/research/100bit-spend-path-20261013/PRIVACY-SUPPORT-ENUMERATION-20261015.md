# C1 eligible-support enumeration (2026-10-15)

This note records integer-index bookkeeping for the current privacy probe. It does not compute field values, test matrix rank, or claim that the supports imply any rank statement.

The source is [`privacy-wide/probe.rs`](privacy-wide/probe.rs), SHA-256 `54ec15ab6aa9205d3a07d4de56680cd301b6fdfb769dd6281d17b2fb7a13b531`. The `ACTIVE` mask and `inactive(r)` are at lines 17–25; `eligible(c,r)` is at lines 27–48. The D18 row-to-coefficient permutation is `d18_transport` at lines 2932–2939. `c1_raw_ranks` at lines 3038–3053 excludes row 1023, while retaining every other eligible row and subtracting the pivot row for inactive rows.

The reproducible enumerator is [`privacy-wide/support_enumeration.py`](privacy-wide/support_enumeration.py), SHA-256 `d5821a455755754c5f05fd9f5d8d4c52b086c0a2c4006aeef9fd46987c3d3e09`. It checks both the source hash and the retained log hash, reads `ACTIVE` from the pinned source, applies the predicate and D18 digit permutation, and checks each computed coefficient set against all 16 saved `Z5_ELIGIBLE_IMAGES` entries. Run it with Python 3; complete per-column coefficient runs and per-residue quotient runs are saved in [`privacy-wide/support_enumeration_output.txt`](privacy-wide/support_enumeration_output.txt), SHA-256 `b162aab8b69689d9cde5aad0075d60be4ecce2f00ad773aa159e5306eca2ebe6`.

| C1 column(s) | Eligible rows after excluding row 1023 | D18 coefficient runs | Number of runs |
|---|---:|---|---:|
| 0–1 | 221 each | same support | 37 |
| 2 | 222 | column 0–1 support plus coefficient 511 | 37 |
| 3–8 | 223 each | column 2 pattern plus coefficient 447 | 38 |
| 9 | 247 | column 3–8 pattern plus its listed high-column exceptions | 46 |
| 10 | 248 | column 9 pattern plus coefficient 703 | 47 |
| 11–15 | 258 each | column 10 pattern plus coefficient 191 and the logged tail changes | 47 |

The common support across all 16 columns has 221 elements. In row coordinates it is the intersection computed by the script; after transport its contiguous coefficient runs are `15, 30–31, 46–47, 62, 207, 222–223, 238–239, 254, 271, 286–287, 302–303, 318, 463, 478–479, 494–495, 510, 527, 542–543, 558–559, 574, 719, 734–735, 750–751, 766–767, 783, 798–799, 814–815, 830, 832–846, 848–861, 864–877, 880–893, 895–910, 912–925, 928–941, 944–957, 960–1022`.

For residue `j mod 4`, the script groups columns that have identical quotient-index run sets (`q = (j - residue)/4`): residues 0 and 1 have quotient indices 208–255 for all columns (48 each); residue 2 has 63 indices for columns 0–8 and 75 for 9–15; residue 3 has 62 for columns 0–1, 63 for column 2, 64 for 3–8, 76 for 9, 77 for 10, and 87 for 11–15. The exact quotient runs for every column and residue are in the output file.

Row 1023 is inactive and eligible for all 16 columns. D18 maps it to coefficient 1023. The C1 support construction nevertheless excludes it as the balancing pivot; inactive non-pivot rows remain in the support and are differenced against row 1023. Column-specific eligibility changes the support sizes above, while the intersection remains 221 elements.

The independent retained diagnostic is `evidence/privacy-wide/wide-full-g0.log`, SHA-256 `d42d7fade8178f4de1b166b7eaeacf5904bc3b77a17ba42b5613c6eaee83a70b`; its 16 `Z5_ELIGIBLE_IMAGES` coefficient sets match the enumerator exactly. This is a consistency check of finite index sets only.
