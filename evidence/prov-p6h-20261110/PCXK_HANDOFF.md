# PCXK_ handoff (P6h: credited theorems re-verified at the default heartbeat limit)

Claim established: all 78 PRVEq files flagged by PCXJ (1174 theorems above 200000) compile with exit 0 when the raised option is confined to the inlined Aeneas emission and every `maxHeartbeats N in` is at most 200000. 1514 theorems, 0 heartbeat failures, every #print axioms standard (PCXK_RESULTS.json, PCXK_L001..L025 receipts). Heartbeat audit on the corrected copies: 0 theorems above 200000 (PCXK_HEARTBEATS.json). PCXK_FAILED.json has 0 failed theorems, so no heartbeat demotions and no proof changes.

Recount (PCXK_COUNTS.json, `python3 -I -B PCXK_recount.py --demote PCXK_FAILED.json`): settled 1096, not settled 542, other 69 of 1707; rows settled-only 120 of 599 (identical to PCXJ). The 205 named credited theorems are therefore no longer pending.

Owner decision 2026-11-10 (row ReviewedTranscription-PublicPreparation.public_bytes withdrawn): PCXK_FAILED.json section trust_row_withdrawn lists 3 definitions (AspisR1PublicPreparation.Funs: public_transcript, and the two closure call_once instance records) demoted to OPEN. Count effect on the three numbers: none, since they are outside the cone and the PCXH baseline universe. FieldDerives untouched.

Ran: 25 Lean scopes (60 budget), 0 extraction, 6G/8G swap 0, max peak RSS 5.94 GiB, max file wall 74.6 s. Caveat: copies are compiled against the L187 closure plus PCXG_exports, not each original workspace; originals changed only by the heartbeat edit and appended print lines.

Target not yet established
