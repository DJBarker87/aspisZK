# NHJ entry spine — final scoped result

**14 new CLOSED rows /9 functions; zero complete TX1/TX2 paths. Target not yet established.** Authoritative input is the unchanged NGZ599-row ledger:303 CLOSED/296 OPEN; additive NHJ result317 CLOSED/282 OPEN. Snapshot is expressly OPEN. No security, privacy or custody theorem is promoted.

## Entry roots and distance

| Row | Function | Status | Owner / exact remaining obligation |
|---|---|---|---|
| TX1:330 | `programs/r1-cost-probe/src/lib.rs::process_r1_cost_probe_instruction` | OPEN | NHJ / lead: Full original AccountInfo/data forwarding, route domain, child process certificate and model/native/effects composition. |
| TX1:333 | `programs/r1-cost-probe/src/r1_pool_adapter.rs::process` | OPEN | NHJ / lead: Route predicate now CLOSED for all lengths. Still needs exact stage schedule, lifecycle rejection and both child Results/effects packets. |
| TX1:344 | `programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage1` | OPEN | NHJ / lead: Snapshot full cohort borrow-result association remains OPEN; three snapshot calls, SDK mutable write and SAME1768 checkpoint/cleanup, then CLOSED owned-stage packet. |
| TX1:345 | `programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage1_owned` | OPEN | NHJ / lead: All account guards/data/canonical decode domains and proof-prefix validation, first_decoded, exact result/cleanup order. |
| TX1:328 | `programs/r1-cost-probe/src/lib.rs::first_decoded` | OPEN | NHJ / lead: SAME public/proof/split and deployed None observer; candidate tx1 packet plus error mapping/logging and full result/cleanup. |
| TX1:094 | `crates/aspis-r1-cost-probe/src/candidate.rs::tx1` | OPEN | NFW_: Candidate tx1 composed packet and exact public/proof/S2/split/prepared/query/checkpoint domains needed by first_decoded. |
| TX2:213 | `programs/r1-cost-probe/src/lib.rs::process_r1_cost_probe_instruction` | OPEN | NHJ / lead: Full original AccountInfo/data forwarding, ASQ8 route domain and child process certificate. |
| TX2:221 | `programs/r1-cost-probe/src/r1_pool_adapter.rs::process` | OPEN | NHJ / lead: Route predicate now CLOSED; ASQ8/stage2 schedule and exact child Result/effects packet remain. |
| TX2:240 | `programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage2` | OPEN | NHJ / lead: Empty-clear trust still pending; seven snapshot cohort joins and stage2_owned missing. Clock reply/slot continuation is proved locally; syscall VALUE remains accepted runtime trust. |
| TX2:241 | `programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage2_owned` | OPEN | NHJ / lead: Full validate_asq8 authentication/data/statement provenance, SAME tx2 inputs, error callback and emit_result composition. |
| TX2:064 | `crates/aspis-r1-cost-probe/src/candidate.rs::tx2_authenticated` | OPEN | NFW_: Authenticated candidate packet; public/proof/checkpoint exact domains passed by stage2_owned. |
| TX2:065 | `crates/aspis-r1-cost-probe/src/candidate.rs::tx2_common` | OPEN | NFW_: Common TX2 packet and all prepared/resume/query domains with None observer. |
| TX2:115 | `crates/aspis-r1-cost-probe/src/verifier.rs::finish_relation` | OPEN | NFW_ / lead to confirm: Exact caller-established finish_relation input/invariant and composed relation checker; no accepted-run hypothesis. |

## Adjacent helper packets

| Member | Rows / status | Distance removed or retained |
|---|---|---|
| readonly_meta_ok / require_readonly_account | TX2:223/236 CLOSED | Exact metadata, constructor coverage and first-error local log |
| OwnedAccount::data / data_len | TX1:335/336, TX2:229/230 CLOSED | SAME allocation or canonical deferred error; full Result clone transport |
| require_verifier_checkpoint | TX1:341/TX2:238 CLOSED | Actual metadata prefix then CLOSED length packet and size1768 |
| require_distinct_accounts | TX1:339/TX2:235 CLOSED | N3/N7 same key references, one native invariant step plus existing induction |
| pool_program_id / registry_program_id | TX2:220/225 CLOSED | Named default/devnet rodata slots, actual RPx IDa/FIp pipeline specialization |
| pool_route::admitted | TX1:331/TX2:214 CLOSED | All lengths, physical2/4-byte windows, complete unbounded emitted/cohort association |
| snapshot | TX1:343/TX2:239 OPEN | Allocation/copy/header/SDK cleanup and producer domains proved; legal borrow-error path is not joined to actual Entry.snapshot |
| lib.rs::error | TX1:NGB001/TX2:211 OPEN | Eight labels retained; full Debug formatter callback/native bytes/cleanup association quarantined or missing |
| authenticate_asq8_accounts / authenticate_invariant_release_registry | OPEN | Nullable single-guard step and first5 registry guards proved; full decoder/PDA/first-error suffix packets missing |

first is reachability-excluded by C3-BIN; no work spent on it. first_decoded and candidate tx1/tx2 are real external boundary obligations, not assumed packets. Every root retains its actual argument/physical domain. No SameExecution wrapper, parent acceptance or output-equality premise is introduced. See NHJ_REMAINING.md for each member and the unused-budget review.
