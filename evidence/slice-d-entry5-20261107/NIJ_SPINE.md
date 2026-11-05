# NIJ entry spine — inherited baseline

**NIJ:1 newly CLOSED row/function (TX2:202); inherited NHY14 rows/13 functions and NHJ14 rows retained separately. Zero complete TX1/TX2 paths; target not established.** NHY delta is additive against unchanged NHO599-row ledger (335 CLOSED/264 OPEN →349/250); NHJ14-row delta is retained separately, without duplicating credit. No security, privacy or custody theorem is promoted.

## Entry roots and distance

| Row | Function | Status | Owner / exact remaining obligation |
|---|---|---|---|
| TX1:330 | `programs/r1-cost-probe/src/lib.rs::process_r1_cost_probe_instruction` | OPEN | NHJ / lead: Full original AccountInfo/data forwarding, route domain, child process certificate and model/native/effects composition. |
| TX1:333 | `programs/r1-cost-probe/src/r1_pool_adapter.rs::process` | OPEN | NHJ / lead: Route predicate now CLOSED for all lengths. Still needs exact stage schedule, lifecycle rejection and both child Results/effects packets. |
| TX1:344 | `programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage1` | OPEN | NHJ / lead: Snapshot packet is CLOSED on the retained SAME entry-heap domain; compose three snapshot calls, SDK mutable write and SAME1768 checkpoint/cleanup, then CLOSED owned-stage packet. |
| TX1:345 | `programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage1_owned` | OPEN | NHJ / lead: All account guards/data/canonical decode domains and proof-prefix validation, first_decoded, exact result/cleanup order. |
| TX1:328 | `programs/r1-cost-probe/src/lib.rs::first_decoded` | OPEN | NHJ / lead: SAME public/proof/split and deployed None observer; candidate tx1 packet plus error mapping/logging and full result/cleanup. |
| TX1:094 | `crates/aspis-r1-cost-probe/src/candidate.rs::tx1` | OPEN | NFW_: Candidate tx1 composed packet and exact public/proof/S2/split/prepared/query/checkpoint domains needed by first_decoded. |
| TX2:213 | `programs/r1-cost-probe/src/lib.rs::process_r1_cost_probe_instruction` | OPEN | NHJ / lead: Full original AccountInfo/data forwarding, ASQ8 route domain and child process certificate. |
| TX2:221 | `programs/r1-cost-probe/src/r1_pool_adapter.rs::process` | OPEN | NHJ / lead: Route predicate now CLOSED; ASQ8/stage2 schedule and exact child Result/effects packet remain. |
| TX2:240 | `programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage2` | OPEN | NHJ / lead: RuntimeReturnDataClear accepted; compose seven CLOSED snapshot packets and stage2_owned. Clock reply/slot continuation is proved locally; syscall VALUE remains accepted runtime trust. |
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
| snapshot | TX1:343/TX2:239 CLOSED under (y)/(ak) | Both-arm SDK/clone log K005/006; all-usize descriptor K008/009; NHY_SnapshotHeader.chain and NHY_SnapshotJoin.source. SAME computed entry heap has counter0; SDK15 derives acquisition/restored heap. Generic borrow-error arm remains explicit. Native/model/caller-size packets reused by SHA. |
| lib.rs::error | TX1:NGB001/TX2:211 OPEN | Eight labels retained; native String writer/callback, byte production and cleanup still OPEN; DebugLog calibration is quarantined for deployed error credit |
| authenticate_asq8_accounts / authenticate_invariant_release_registry | OPEN | Nullable single-guard step and first5 registry guards proved; full decoder/PDA/first-error suffix packets missing |

first is reachability-excluded by C3-BIN; no work spent on it. first_decoded and candidate tx1/tx2 are real external boundary obligations, not assumed packets. Every root retains its actual argument/physical domain. No SameExecution wrapper, parent acceptance or output-equality premise is introduced. See NHJ_REMAINING.md for each member and the unused-budget review.

## Distance after registry helper stage

TX1 still needs owned-stage exact statement/proof provenance, first_decoded error/candidate boundary, three snapshot physical-domain links and checkpoint write/cleanup, then process/entry routing. TX2 still needs full authentication, stage2_owned/candidate/emit/error packets, seven snapshot physical-domain links, empty clear and clock continuation, then process/entry routing. The leaf certificate does not supply a successful child or remove the actual caller provenance obligation.


Nine authentication dependencies now CLOSED: TX2:151 policy validator;192 status conversion;193/195 no-retirement V1/V2;197/198 registry V1 immutable/paused;199/200 V2 immutable/paused;205 fixed32 zero binding. Complete typed input domains, including invalid flags/status bytes, are retained. Policy includes all three failure labels; no validation-success premise. K028/029,030..042/044,046/047; coherent source/pipeline models L025/027..029/034 and combined L045, raw/NFX L031/032/046. K043 is an excluded feature-mismatched negative, replaced by K044 under default features. Full decoder/native auth rows remain OPEN.

Error callback progress: eight isolated native Debug label loggers pass, each has a semantic failing control; Parse has its rename stability pair. These prove label argument/count/length forwarding only. The allocated String implementation and native final msg! byte/cleanup join remain OPEN after K004/007/010 timeouts. NHY_ErrorFragments, NHY_StringAppend provide symbolic label/frame laws; no lib::error credit.

Current-format decoder progress: original256/320-byte buffers transport to64/16-byte local windows at arbitrary legal offsets (K049..056); controls fail. Retained NCX validators are under revalidation, not yet admitted. Full native record construction, first-error suffix and same SDK call association remain OPEN. V1 models cannot use the current V2-only extraction as a stand-in.

Validator stage: TX2:207 and209 are now CLOSED. Retained NCX_K004/005 and006/007 are reconstructed and revalidated by immutable patch/graph/lock/KMX hashes, no passing proof replay. Their safe-reference bodies match the exact E002 extracted bodies token for token after namespace qualification only. Full typed record and12-error ports are two-sided; native-domain laws L058 and combined L063/raw L064 pass. The actual decoder roots (201..204), both authentication parents and both owned-stage roots remain OPEN.

## Current registry decoder closed

TX2:204 decode_verifier_registry_v2 is CLOSED under(y)/(ai)/(ak), all input slice lengths and contents. No prefix/header/validation-success premise. Exact first-error K057/058, same ORIGINAL256-byte cast/word caller windows K049/050 and053/054, complete same-record validator argument logs K093/094, all Result/errors/returned fields K063/064, CLOSED validator209. All7 arrays,2 words and3 scalars are enumerated by NHY_registry_check.py; no64/16-byte restriction on original account. NHY_RecordExt turns arbitrary field/byte observations into full record equality. NHY_RegistryModel.source proves the universal natural parser, and NHY_RegistryJoin.source/cohort binds actual NCX_Install.op33 and preserves digest/error43/44. Final combined L079, raw/NFX L080 pass with standard axioms. The separate current entry decoder202 remains OPEN after K092 full Result carrier timeout; K095/096 argument-only cuts pass and do not close it.

TX2 authentication distance is reduced by one complete decoder child. Both V1 decoders and current entry decoder, complete PDA/first-error composition and authentication parent still remain. Every actual PDA seed call site has a native argument/value/length/domain packet and matched failing control (K069..086); reply mapping K087/088 covers all SDK errors. These are syscall-argument/reply observations only, not a PDA-value or canonicality theorem.

## Final distance and budget checkpoint

CLOSED NHY rows: TX1:343, TX2:239,151,192,193,195,197,198,199,200,205,207,209,204. Snapshot leaf domain is explicit; neither wrapper has its physical join yet. Current registry204 is one complete decoder child, not a full authentication path. Current entry202 now has an SSA Result packet K108/109, but its full first-error/model/source join remains OPEN.

One real1768-byte checkpoint iteration K114/115 is native-green; induction and parent association remain. Both owned stages have native prefix/span/tail support, but no parent certificate. Exact outgoing runtime pointer/length arguments and empty clear invocation are observed by K116/117; String production and empty-clear effect remain OPEN. Full remaining table is NHY_REMAINING.md.

120 K slots and80 L slots consumed conservatively (69 compiles,10 audits,1 no-launch preflight);0/2 extractions because the mandatory stager has no helper/program roots.51 native passes,52 semantic failures (includes own corrected-reference and excluded-config findings),11 excluded timeouts,6 input/compile failures. Every matched control is checked; no timeout or cap was raised, no memory kill or swap. Peak RSS6,390,764KiB native and7,024,744KiB formal. Parent roots remain OPEN, as do both complete entry paths.

## NIJ exact path distance after decoder stage

TX1 still needs six OPEN spine rows:330 entry →333 process →344 SDK stage1 →345 stage1_owned →328 first_decoded →094 candidate tx1. TX2 still needs seven OPEN spine rows:213 entry →221 process →240 SDK stage2 →241 stage2_owned →064 tx2_authenticated →065 tx2_common →115 finish_relation. These are exact unresolved row counts on the pinned inherited ledger, not estimates of proof effort. Candidate implementation work is NIH_/NID_/NIG_/lead; NIJ only consumes exact NHL/NHT model boundaries.

Shared side gaps remain: two error occurrences (one function), two authentication parents, V1 decoder/validator suffixes and active-at helpers. Current registry204 and current entry202 are CLOSED. Empty-clear trust distance is zero under(am); wrappers still owe their physical joins. New zero-loop induction is support for existing342, not new row credit. No complete path can be inferred from364/599 CLOSED rows.
