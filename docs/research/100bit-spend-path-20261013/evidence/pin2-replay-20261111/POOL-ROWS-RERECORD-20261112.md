# Pool ledger rows re-recorded at the Aspis freeze (3d700effcab, Pool ELF 0553a8bd5ef5...)

Written 2026-11-12T05:58Z by the Stream A lead. Tool record; nothing proved; no row changes status. Target not yet established.

**Convention.** The PCE ledger's frozen_body_sha256 is the sha256 of the function's body block bytes (tree-sitter body node: from the opening brace to the matching closing brace) at the frozen revision (NIK_census.py line 58). I reproduced all six pinned hashes under that convention at c7593d23fdc (Pool unchanged between b936275 and the pin), so the frozen figures below are comparable. zk-73's list (evidence/aspis-freeze-20261112/pool/pool-fn-changes.tsv at 2fb497985be) uses whole-fn-line hashing; its changed/unchanged verdicts agree with mine function by function. Tool: scratchpad poolhash.py (copied beside this note).

| Row | Function | Pin lines | Frozen lines | Body changed | Frozen body sha256 |
|---|---|---|---|---|---|
| POOL:285 | history.rs::validate_root_page_bytes | 119-175 | 131-187 | yes (one line: page check via page_bytes_are_zero) | e22866a738224c99dadba97fdc9abee9331c964df28aa36060af549d54038db7 |
| POOL:301 | pair_forest.rs::account_is_zeroed_program_page | 806-815 | 806-815 | yes (one line) | 93389ae7444baad3959ffe02f16a72b6da59a915c7c08e7e4778a85c665e5944 |
| POOL:333 | pair_forest.rs::require_program_owned_zeroed | 400-415 | 400-415 | yes (one line) | 5e7b2be0d055511f2df0032ad59ada9bbb7255f011c3e60414685293e3668e11 |
| POOL:340 | pair_forest.rs::validate_lane_current_page | 817-860 | 817-860 | no (hash fc48818f… unchanged; it calls POOL:301) | fc48818f923fdf74a26594fb0d94dc41203290677625f768e9b7bb01f45aa8bf |
| POOL:322 | pair_forest.rs::plan_pair_forest_spend_layout_v1 | 1218-1319 | 1218-1319 | no | 51801b29cf49055552b83fd3e82d970e3682e77e41617cc76778d1d88c220c9b |
| POOL:330 | pair_forest.rs::process_pair_forest_terminal_with_verifier_v1 | 1615-1821 | 1615-1821 | no | 49900881a1301d8138c9e1589ca3821f8a0e9d21f2b40d16f4e115905dd826f5 |
| (new) | history.rs::page_bytes_are_zero | - | 60-62 | new; callee of 285, 301, 333 | cc7aecce51f7c4deb86cb2e35c881a2fa852bb988faf1876beb93d6e95b98cfb |

Correction to POOL-PAGECHECK-DEPS-20261111.md: it listed POOL:340 among the three functions whose body changes; the three are 285, 301 and 333. POOL:340 is a caller of 301 only. history.rs::validate_new_page_account also changed (296-309) but has no ledger row (not on the spend path; checked against NKZ_INVENTORY).

**Status.** All six stay OPEN, as they were. For Aspis, 285/301/333 need a new ledger row keyed on the frozen hash plus a row for page_bytes_are_zero; 340/322/330 keep their pin keys (body identical) but their caller clauses to 301 (340) and 285/333 (322/330 by packet) must be re-derived against the new callee bodies.

**Consequence for CLOSED rows, statement crate.** The translatability pass reshaped five statement-crate functions that the Pool links and that are CLOSED Pool ledger rows at 4bb3b3f: POOL:201 validate_master, POOL:192 decode_pool_v1_pair_forest_master_v1, POOL:190 decode_pool_v1_pair_forest_checkpoint_v1, POOL:216 decode_pool_v1_pair_verified_afterstate_v1, and the live-snapshot decoder (no ledger row of its own; its encode/validate rows 226/227 are unchanged). Their R1 closures stand for R1. For Aspis they do NOT carry over: the ledger keys on the body hash, and the bodies differ. The behaviour-equality argument for each is in ASPIS-FREEZE-DIFF-REVIEW-20261112.md (same accepted set, same error variant; reviewer argument plus the author's differential tests, not a proof). In the Pool ELF three functions differ in normalised body (master, checkpoint and verified-afterstate decoders) and decode_afterstate_frontier_v1 is new; the other 284 are equal (zk-73). Re-closure of those four rows on the frozen bodies is owed before any Aspis Pool-row credit is counted. Nothing in the R1 ledger is reduced by this.
