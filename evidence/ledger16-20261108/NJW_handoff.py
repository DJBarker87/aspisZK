from pathlib import Path
import json,lzma,subprocess
E=Path(__file__).resolve().parent
J=lambda p:json.loads(lzma.decompress(p.read_bytes())if p.suffix=='.xz'else p.read_bytes())
A=J(E/'NJW_AUDIT.json');S=J(E/'NJW_SCAN.json');P=J(E/'NJW_PREDECESSOR_COMPARISON.json');X=J(E/'NJW_EXPORT.json');rs=A['resources'];seed=J(E/'NJW_CACHE_IMPORTS.json.xz');V=J(E/'NJW_VALIDATION.json')
text=f'''# NJW ledger16 ninth all-slices composition handoff

**Target not yet established. Gate PASS:484 CLOSED /0 QUALIFIED /115 OPEN of599.** Branch codex/cx-ledger16-20261108. Local stage commits; no push. Only own NJW modules/receipts authored. No shipped/existing-proof/trust-row/sibling/session-A/key/fund changes.

## Exact admission versus NJO

Exactly21 new occurrences: NJI TX2:150,157,206,208(4); NJM TX1:133,134,142(3); NJP TX1:306,305(2); NJL TX1:208,209,214,216,217,219,227,228,229,231,244,247(12). Every row was OPEN in NJO463/136. Ledger13/14 packets were compared against NJO complete obligations; no delta or count reused. All190 original caller clauses and original unit/domain/hypothesis fields retained verbatim, with full kernel statements and canonical primary roots in NJW_CANDIDATE_REVIEW.json.42 explicit own-domain/unit-context clauses recorded at actual parents in NJW_PARENT_CLAUSES.json; internally composed own domains have named root discharges, upstream provenance remains OPEN. No unsubmitted parent promoted.

NJI-F1 checked individually: all4candidate bodies are emitted nonopaque definitions from the pinned raw Funs, selected Core/Master and the exact root raw/body chains (NJW_NJI_EMISSION.json). The four omitted OTHER decoder bodies TX2:152/153/201/203 remain OPEN. NJM rounds’ only Prop input is reviewed NJG K016–019(ai)(5) native transcription, explicitly inventoried; parse/getter/canonical/frame bounds and CLOSED child Results are internally derived. No endpoint/child-success/Run/arbitrary dictionary root hypothesis. NJL’s NGK/NIU/NJB/NIX owners match NJO exactly; no duplicated proof or owner.

Native evidence revalidated read-only:52new-packet solver runs plus5inherited NJM assertion/control pairs, frozen graph/unchanged lock/offline/deployed features, exact KMX configuration and matching failures. NJP K008/009 provenance metadata difference is disclosed; harness source identical. Stale K010–012 compression comment labels are superseded by actual K057–059. NJI Result-contract shape controls retained. No Kani or extraction launched. Historical timeout/quarantine/failed/uncompiled material remains excluded. NJR/NJN support gets zero credit. P6/D188 optionA is RECLASSIFICATION, never removal.

## Combined gate and pins

L001 composes NJO+NJI+NJM+NJP+NJL and every imported support module with AspisR1.RPx_Deployed.deployed. L002 prints all{A['required_roots']} roots’ complete statements/owners; all9214NJO roots unchanged. L003–006 compile/link unchanged adapted NFX/raw drivers, optimized links. L007 replays SAME8fixtures in SAME proof binary used by every raw group L009–038. L008 NFX exit0: {S['modules']}modules/{S['declarations']}declarations/{S['references']}references, zero dangling, incompatible/duplicate canonical owners or import mismatches; {S['compatible_cached_replicas']}compatible theorem-cache replicas disclosed under NJO method.

Raw ax2 audits every{A['required_roots']}root exactly once; only propext/Classical.choice/Quot.sound. NHC_DecodeModel.decoder_error retains raw-standard versus empty collector discrepancy and ACTUAL nonzero audit exit(s){A['retained_nonzero_audit_exits']} under(ab′)(3); no exit relabelled. L039 prints candidate roots/cuts/actual emitted definitions and axioms; no new top theorem. L040 pins full selected closure: all{P['previous_files']}NJO selected files match, zero variants; {P['added_files']}new selected files. No unchanged full regression rerun or cold release claim.

## Physical distance and rulings

(ao)(3)(b):38/53CLOSED,15OPEN. (c):446/546CLOSED,100OPEN. Both shortest actual transaction spines retain6OPEN rows/ancestors; TX2 endpoint115 is conditionally CLOSED. NJW_PHYSICAL.md/.json recomputes paths, all115OPEN rows grouped by source/live routing, and every named Pool obligation. Live brief: NJQ tx2-decoders2, NJS batch-merkle, NJT claims-queryscan, NJU tx2-native8, NJV multiproof4; no sibling worktree touched.

(av) applies borrow-minimal reference principle; next post-NJL consuming job owns terminal256/finish136; NJT owns129 and066–070. (aw) adds NEW OPEN child supplement NJW-aw-TX2:115-off-domain: SAME-current-byte off-window Err/abort/order law, needed by tx2_common’s case split.115 remains CLOSED AS STATED on SAME-call NIG_FinishInput.Domain; supplement is outside599numbered function occurrences and adds no game/trust premise. No NoBad/history/current-proof persistence or accepted-finish hypothesis. Exact supplement owner remains with lead; NJU overlaps.

K086 RETAINED liveness/abort finding; production reachability/exclusion UNPROVED. Owner(aj)(a) PENDING. Pool NIB-P1..P4/prefix/read-settlement/four held sites/13exclusive owners and21accessor associations remain OPEN by name; no finite complete production inventory follows. RuntimeCpiReadonlyEntry7 unused. RuntimePersistence data-only trust and seven Pool initial-entry fields unchanged. No PDA value row; op38 quantified; digest/error op43/op44.

## Resources, retention and restoration

40/40serial scopes {rs['kinds']};0Kani/0extraction. Every admission exit0 AND allowed:true; all6Ghigh/8Gmax/swap0/tasks64, Lean-M7000. Optional16G aggregation exception unused. Scope wall{rs['wall_seconds']:.6f}s; maximum peakRSS{rs['peak_rss_kib']}KiB; swaps{rs['swaps']}. Exact target/argv/exit/wall/RSS/swap/revision/source/dependency/Aeneas hashes and full printed axioms are in NJW_ATTEMPTS.jsonl and per-scope receipts. No timeout/memory kill, cap increase or unchanged rerun.

Seed{len(seed['files'])}objects/sidecars,{seed['bytes']}bytes copied/hash-checked from retained exports into owned cache. No shared workspace/cache mutation. Own retained export {X.get('export')} ({X['bytes']}bytes); prepend it to NJW_PATHS.json for consumers. Full pins NJW_CLOSURE_PINS.json.xz/NJW_TOOL_PINS.json. Cache never deleted. Packaging/validation PASS:{V['sources_checked']}source snapshots,{V['compressed_sha_pairs']}compressed SHA pairs,{V['input_pins']}input pins; {len(V['mutations'])}overclaim/caller/domain/gate/trust/supplement mutations rejected. Own metadata parser/primary-owner fixes recorded, with no validation relaxation or prover rerun. Transient client lock removed from index and ignored; no live scope affected.

Frozen4bb3b3f5crates/programs/Cargo.lock unchanged in historical-root and research scopes. No ELF rebuild trigger. Inherited only: default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4; devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299; Pool121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548. No binaries/objects/ELFs or files over20MB committed.

Frozen3/deployed headline/L154parameter/narrowedD188/100-bit PER-ATTEMPT/privacy/two transactions unchanged. No headline hypothesis discharged. NJW_REMAINING.md lists all remaining native and Lean-only work; budget exhaustion, not Kani exhaustion, ends this job. Native entry/op9/TX2 common/production Pool association, L187cold release replay and L188artifact/extraction audit remain. **Target not yet established.**
'''
(E/'NJW_HANDOFF.md').write_text(text)
print(json.dumps(dict(stage='handoff',status='PASS',closed=484,open=115)))
