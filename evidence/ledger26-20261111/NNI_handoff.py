from pathlib import Path
import json,lzma,subprocess
E=Path(__file__).resolve().parent
J=lambda n:json.loads((E/('NNI_'+n+'.json')).read_text())
a=J('AUDIT');r=J('RESOURCES');s=J('SCAN');v=J('VALIDATION');p=J('PROVENANCE');host=J('FINAL_HOST');export=J('EXPORT')['export'];binary=a['same_optimized_proof_binary_sha256'];physical=J('PHYSICAL')
text=f'''# NNI ledger26 handoff

Target not yet established. Nineteenth all-slices composition gate PASS: **583 CLOSED /0 QUALIFIED /16 OPEN of599**, basis ledger25 NMQ582/0/17. Only TX1:136 is promoted. No edge or trust item is removed; no Pool row is promoted. Branch codex/cx-ledger26-20261107; local stage commits, no push.

## TX1:136 admitted

Canonical root `AspisR1.NNG_Candidate136.candidate` states literal revision3 `RSL.TX1_136.RowSpec_136 LIB_VLib.library NNG_Producer136.producer`. Fresh actual frozen verify_finish emission NNG_E001 (root r1_semantic::verify_finish, frozen4bb3b3f51e16, pinned source/lock/tools/output) passes the(bc) post-loop audit. Source-tree erasure, same trace observation, concrete representation, all16 raw call slots, actual reached domains and full source-order fold are linked through NNG_TreeEmission, Observed136/DEnvObserved136, PacketContext136/Packet136.closed and DRowSpec136.fold. No child/library/representation parameter remains. The LIB fields are graphs of canonical CLOSED child models, not arbitrary native cuts;18 canonical callee packets and43 original caller/inventory clauses are retained/classified in NNI_CANDIDATE_REVIEW/CLAUSE_REVIEW.

Own finishInputDom remains a caller clause at OPEN TX1:137: publicDigestDom, publicAssetDom, and original Prefix source length≤57607. Prefix carries SAME source/parsed value/parse_eq;137 must supply that from its actual parser. Challenges use canonical carriers from SAME begin; running/masked canonicality, repeated25/26 getter equality and used-array bounds are derived internally. NNG's later137 support/WIP receives no row credit. All Result/error/abort/diverge and ordered-prefix arms are retained. Example/rfl statement checks and #print axioms are in NNI_L011.

## TX2:217 rejected for this gate

NMX_R3_DecoderFold.root and complete reference observation replay against revision3 for every slice length, both final Box allocation outcomes, exact windows/frame and arbitrary native one-step/Lean induction. NCV safe-reference bytes and emitted Funs hashes match the pinned route.18 NMX retained runs and14 inherited NDB component/control runs were checked for actual verdict, expected failure text, frozen offline dependency graph, deployed feature list, unchanged lock and exact KMX patch bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67. K014/API failures and K021/K023 timeouts receive no credit and are not rerun.

Ruling(t) per-shape fidelity is incomplete. K006 is an ensures FAIL and K011 detects modifies violation, while K009 passes on the real body. K010/NMX_shape_stub is a COMPILE FAILURE (`Result<Box<Lane>,ProgramError>` lacks kani::Arbitrary), not the required unimplied caller-assertion FAIL under stub_verified. Excluding that pilot substitution does not complete the stated prerequisite for relying on this contract shape. The used K015/K016 assignment has a distinct Result<(),ProgramError>/mutable digest-array shape: its matched ensures failure is retained, but the full three-part per-shape calibration is not provided. Even omitting redundant length-pair reliance cannot silently waive this second interface obligation. These are missing fidelity evidence, not a counterexample to the source or the Lean reference.0 Kani authority here, so217 stays OPEN with exact certificates/clauses named.

ReviewedTranscription-TX2:217 is recorded ADDED-LEAD-20261107 under(ah), option-A reclassification, unused by any CLOSED row in this gate. The two(bn) rows ReviewedTranscription-TX1:344/TX2:240 are carried verbatim, also unused by CLOSED rows. Nothing is removed.

## Combined gate and resources

NNI_COMBINED_IMPORT includes ledger25, candidate modules, concrete LIB/LIBB/LIBC fields/support, and AspisR1.RPx_Deployed.deployed. **All{a['required_roots']} required roots** raw ax2 standard-only ({a['new_roots']} new); all11401 predecessor statements and owners unchanged. Same optimized proof binary {binary}; same8 fidelity fixtures. Predecessor disjoint/pre-split groups retained, cheap groups20/21 sequentially paired, additions bounded to120 roots/group. The two inherited collector disagreements and the new Acc alias finding/diagnostic remain explicit under(ab')(3)/(ax2); raw walk is authoritative.

NFX scan exit0 over{s['modules']} modules: zero dangling, canonical duplicate owners and import mismatches. {s['cached_replicas']} identical serialized replicas are separately retained. The final additive alias diagnostic is compiled at58, raw-walked at59, then included by the changed combined import/final scan/pin/retention at60. The8 original fixtures and all earlier roots are retained without unchanged replay. First scan L054 failed ONLY the independently sourced expected-import inventory; its zero-dangling/zero-duplicate result,434 findings, original source snapshot and receipt remain.427 committed source variants agreed;7 explicit compiled-source/template choices are recorded, with independent preflight. Corrected-manifest L055 passes; no scanner or shared infrastructure was weakened.

{r['scopes']}/60 serial Lean/link/audit scopes,0 Kani,0 extraction; optional16GiB scope unused. Every scope: fresh ALL codex-* running-scope count<6, host free≥40GB, admission exit0 AND allowed:true,6G/8G/swap0/tasks64; Lean-M7000, optimized link/walker. Exact target/command/source revision/source and selected dependency/Aeneas hashes/exit/wall/RSS/swap/axiom lines are in ATTEMPTS and receipts. Total outer wall{r['wall_seconds']:.3f}s, max RSS{r['peak_rss_kib']}KiB, swaps{r['swaps']}; child audit time is separate. No timeout/OOM/cap increase or unchanged killed-shape rerun. Own import/header/client inventory repairs are explicit; lead reservation/launcher/shim/caches were not modified. Temporary queue holds/submission refusals are not scopes.

Final read-only retention rehashes{host['selected_objects']} selected files, preserving all33962 predecessor files, own copied seeds and5 exported objects. NNI_EXPORT identifies `{export}`; prepend it to NNI_PATHS and import NNI_COMBINED_IMPORT. Imported hashes, object variants and source choices are recorded; cache/TMPDIR retained, zero deletions. Focused coherent cached composition, not a cold frozen-release replay.

## Statement, trust and top status

Canonical RSL revision3 under(bq), including its RETURNED-value functionality clarification, is recorded on top of rev2's allocation-abort corrections. The superseded revision1 rejects_silent claim is retained verbatim as SUPERSEDED, with rejects_silentRet/ref_admits_abort replacement. Expected old/new hashes for all5 merged-module repairs are recorded; no unreplayed repaired344/240/top root is credited. Frozen source, domains except approved R4, trust metric/range and artifact pins are unchanged. (bm)(bn)(bo)(bp)(bq), allocator instantiation and split-B/Realizes five conditions are carried verbatim in NNI_TOP_COMPOSITION. No allocator-success trust item is added.

The historical RZ-STATE OPEN-OWNER request is preserved, superseded by the actual owner decision approving a⊤ and queries on a⊤, with Realizes by eval-of-map over every H and no filtering. Host implementation remains OPEN. TOP:PoolLaws is CLOSED only at the exact concrete `LIBB_PoolNoWrite.laws : NMV_NoWrite.PoolLaws LIBB_PoolLib.library` (combined import/raw standard-only, no extra parameter). No parent fold or G2/top follows automatically. All other host extra parameters/stand-in limits are explicit. TOP:G0 remains OPEN; **headline not composed**. Top records never change599-row totals.

233→016/039 and240→043 are RECLASSIFIED_SPURIOUS_BY_NAME; every edge stays visible. They are u64 checkpoint-sequence little-endian PDA seed conversion and Clock::get, not field conversions/FibreIndex::get. They do not block parent clauses. RuntimeClockSlotBinding gains the exact owned-stage2 consumer text, unchanged statement/status. The real four NLG resume-extents clauses remain OPEN until same-gate canonical241 closes; Root0 is separate TOP:NMF_B/G1c-B and R0rep work. Same-function pairs333/221 and330/213 retain both wrapper dependencies. No parameterized fold is promoted.

K086/(aj)(a) PENDING is carried unchanged in NNI_K086. RuntimePersistence stays data-only; no CPI success/token/system/rent/rollback/readonly/counter-frame law invented. Pool context remains ledger25's read-only PCE15/278 new helpers CLOSED,263 OPEN,119 shared,397 ON; all guard/P1..P4/prefix/read-to-settlement statuses unchanged. Digest/error43/44; PDA38 quantified. Frozen3,L154 statement parameter,narrowedD188,100-bit PER-ATTEMPT,privacy and two transactions unchanged.

{p['historical_verbatim']}

That historical lead line is verbatim. Current conservative same-lexical-method impact is{len(p['current_conservative_affected_CLOSED_rows'])}/583 CLOSED rows;136 reaches133 matching unresolved blobs. The actual gate reachability, not a fresh extraction, supplies this count. NML serialized bucket caveat and rootless059/040 remain explicit. No row is reopened for provenance. The(bk) re-extraction/per-definition-equality release campaign remains a blocker.

## Remaining work and hygiene

NNI_REMAINING lists every16 OPEN member and exact next deliverable, including which needs new Kani.136 has no remaining gate obligation.217's Lean-only reference/induction/frame obligations replay; the missing controls require authority absent from this0Kani refresh. Other principals/folds remain child-first with external missing roots/representations, not additional NNI-owned proof work. All60 scopes were used, including the unexpected collector-alias diagnosis; no unchanged regression was repeated. Cold release replay, L187/L188/source-to-ELF, provenance/equalities and Pool actual execution remain. Target not yet established.

Frozen crates/programs-r1/Cargo.lock exactly4bb3b3f51e16b4525f1d10336e2b0bcbbd775387; Pool exactlyb936275465600469312d1f058cdc91ea2a11f3dc (actual git byte comparisons). No shipped change or ELF rebuild trigger. Inherited, not newly rebuilt: default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4; devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299; Pool e0e49c344d35575116c0359450315ea4334bfb03006551727f67c04a8cfe09dc.

Independent integrity validation: {v['compressed_sha_pairs']} compressed SHA pairs,{v['source_snapshots']} source snapshots,{v['row_root_references']} row-root references;6/6 rejecting controls. Every file≤20MB, larger text losslessly xz-compressed with original SHA. Transcripts are summarised one line per scope. Own transient CLIENT_ACTIVE was accidentally included in an intermediate commit and removed; no transient guard is delivered. No binary/object/ELF, sibling/session-A worktree edit, wallet/key/account/fund/authority action or push.

Read NNI_LEDGER_DELTA.json, NNI_CANDIDATE_REVIEW.json, NNI_CLAUSE_REVIEW.json, NNI_PHYSICAL.md, NNI_REMAINING.md, NNI_TOP_COMPOSITION.json, NNI_AUDIT.json, NNI_SCAN.json, NNI_PROVENANCE.json, NNI_VALIDATION.json and NNI_ATTEMPTS.jsonl. Final evidence commit is the revision containing this handoff.
'''
(E/'NNI_HANDOFF.md').write_text(text)
print('Handoff written; target not yet established')
