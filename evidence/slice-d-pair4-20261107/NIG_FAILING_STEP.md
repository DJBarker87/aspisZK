# NIG failing steps

NIG_K001: own harness duplicate Vec import (KMX already imports Vec); compiler error, no proof credit. Fixed without weakening validation in K002.

All open stages retain exact NHX_REMAINING obligations; no successful child premise introduced. Further failures are appended with receipts.

NIG_K002: prefix_frame Box64 initializer/native resize shape TIMEOUT90s,95.67s wall,6346424KiB,swap0. No credit. Replacement K003 separates pre-state construction using SAME successful reserve plus valid zeroed storage, selected arbitrary old cell; one resize step with unwind6. No unchanged retry or cap increase.

NIG_K003: arbitrary-prefix frame after native reserve and zeroed backing TIMEOUT90s;92.80s wall,6354684KiB,swap0. No credit. Further native split fixes prefix in disjoint two-length intervals; first checks largest62/63 interval, not unchanged shape. Full64 initialization remains OPEN until all intervals compose.

NIG_K004: narrowed62/63 prefix with symbolic old-cell observation also TIMEOUT90s,92.57s wall,6354588KiB,swap0. No credit. K005 isolates only the newly initialized cell; uses valid zeroed backing and actual resize, leaves SAME reserve composition open.

NIG_K005: arbitrary-prefix new-cell observation on zeroed64 backing TIMEOUT90s (95.45s,6354552KiB,swap0). K006 specialized p63 passed; K007 corruption failed, restricted support only. K008 high-prefix56..63 initialized-prefix observation with arbitrary overwritten spare cell TIMEOUT90s (96.45s,6353744KiB,swap0); no credit. No old timeout rerun unchanged.

Stage4: K108 combined ownership/control prefix exceeded90s; classified tool limit, excluded. Split into guard109/110, initial111/112 and argument-edge113/114 records; all positives passed and corruption controls failed. K119/120 full finish source control passed/failed within the unchanged90s solver cap. No native budget remains. L038/041 geometry simplifier left a typed loop match; L043 diagnosed curried emitted body; L044 only redundant final tactic; corrected L045 passes via two symbolic body steps and terminal step. L039 filled dotted Result constructor ambiguity corrected L042. L048 unicode arrow lexer error corrected L049. No failed declaration is credited.
