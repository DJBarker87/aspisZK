from pathlib import Path
import json,lzma
E=Path(__file__).resolve().parent
J=lambda n:json.loads((E/n).read_text())
a=J('NKH_AUDIT.json');assert a['full_composition_pass']
r=J('NKH_RESOURCES.json');p=J('NKH_PHYSICAL.json');pin=J('NKH_PREDECESSOR_COMPARISON.json');ex=J('NKH_EXPORT.json');matcher=J('NKH_MATCHER_OWNERS.json')
text=f'''# NKH ledger18 eleventh all-slices composition handoff

**Target not yet established. Composition gate PASS:542 CLOSED /0 QUALIFIED /57 OPEN of599.** Branch codex/cx-ledger18-20261107; stage commits only, no push.

## Admission and exact scope

Exactly28new occurrences against NKC514/85: NJZ15,NKD8,NJX5. NKH_LEDGER_DELTA.json enumerates each complete obligation/body identity, kernel statement, canonical owner and original caller clause. No ledger15 delta reused or double count.66explicit own-domain/unit-context parent clauses retained; upstream provenance does not close an unsubmitted parent. NJX uses unchanged NKC/NJL helpers at SAME constructed lambda/powers/cache/opened/high/digest arguments. No direct NJL-owned row child appears in its five submitted canonical lists. Spurious-by-name069→202 stays visible under(az)(1); derived QueryScan::default is distinct.

(aw) NJW-aw-TX2:115-off-domain CLOSED outside599 by NJU_GeneralFinishRoot.finish/ported, SAME nativeG/full Result/ordered prefix, arbitrary current raw words at final length2048; off raw windows gives Err/abort. No NoBad/history/persistence/success premise. Original115 remains CLOSED as stated; TX2:065/124 remain OPEN. NJU source-only resume/common roots receive no row credit.

NJZ echeck189 reviewed under(ah)/(ay): every segment Result/error/rejection arm, complete returned record, and returned-Result fidelity controls. Reader native credit ONLY N4/16/32 on1768backing at actual U11/S2 callers; no genericN/S1/backing4840 credit. NKD Transcript ONLY deployedSolanaDigest; exact byte slices/reply forwarding, digest VALUE stays existing runtime trust. Read-only review reuses100native receipts,41direct matched pairs,23inherited pair citations and actual returned-array/PoolTree controls. Frozen graph/offline/unchanged lock/deployed features/exact KMX retained; no new Kani/extraction, multiplication, timeout or quarantined/suspended credit.

## Combined gate and recovery

L001 combined NKC+NJZ+NKD+NJX+NJU+AspisR1.RPx_Deployed.deployed PASS. L002 plus repaired L040 review print all10066complete statements/canonical owners; all9846NKC roots unchanged. L040 prints {len(matcher['roots'])}unique JFw_Validator/JFw_Record matcher owners. L008NFX exit0:16128modules,746657declarations,26636890references; zero dangling/incompatible/canonical duplicate owners/import mismatches;2037compatible cached theorem replicas disclosed.

All10066roots raw ax2 audited exactly once, standard propext/Classical.choice/Quot.sound only, SAME optimized binary and SAME eight fixtures. NHC_DecodeModel.decoder_error raw-standard/collector disagreement retained under(ab')(3); actual nonzero exits {a['retained_nonzero_audit_exits']}, never relabelled. L040 pins full selected closure: {pin['same_predecessor_files']}predecessor files unchanged, {pin['added_files']}added, zero mismatch. Retained export {ex['export']} ({ex['bytes']}bytes); prepend it to NKH_PATHS.json. This is coherent focused composition, not cold release replay.

Original L025 ENOSPC remains unresolved with unknown child metrics. Lead restored host capacity; L026 explicitly resubmitted batch16 after this environment change.5367completed raw roots reused; only4699missing roots audited. L026–037 cover16–27; L038 serially covers28/29; L039diagnostic failed (reserved local name/overbroad matcher); repaired L040compiles one module then pins closure serially. NKH_REVIEW_REPAIR.json records the diagnostic repair; no theorem statement changed. No unchanged timeout/memory retry.

## Physical distances, trust and remaining target

(ao)(3)(b)38/53CLOSED,15OPEN; (c)504/546CLOSED,42OPEN. Both shortest spines retain6OPEN rows/ancestors. NKH_PHYSICAL.md/.json lists all57OPEN rows by source with supplied NKA/NKB/NKE/NKF/NKG routing and explicit unowned rows; NKH_REMAINING.md distinguishes native cuts/controls from Lean-only substitution/domain/frame/induction/assembly. All named Pool NIB-P1..P4/prefix/read-settlement/fourheldsites/13exclusiveowners/21accessor associations remain OPEN; no complete finite deployed-root Pool inventory claimed.

Only ReviewedTranscription NJZ-RT189/201/202/203/204 added, P6/D188 option-A RECLASSIFICATION, never removal. Runtime/cryptographic rows unchanged. RuntimePersistence data-only; initial Pool entry seven fields; RuntimeCpiReadonlyEntry7 unused; no PDA value row; op38quantified,digest/error43/44. K086 retained liveness/abort finding; production reachability/exclusion UNPROVED. Owner(aj)(a) PENDING. Actual entry/op9/native parent/Pool continuation,L187cold replay,L188artifact/extraction remain. Frozen3/deployed headline/L154parameter/narrowedD188/100-bitPER-ATTEMPT/privacy/two transactions unchanged.

## Resources and retention

40/40serial scopes,39complete receipts plus original unresolved L025;0Kani/0extraction. All admission exit0 AND allowed:true;6Ghigh/8Gmax/swap0/tasks64,Lean-M7000. Optional16G unused. Complete recorded wall {r['wall_seconds']:.6f}s; max peakRSS {r['peak_rss_kib']}KiB; swaps0; L025metrics unavailable. Exact targets/argv/source revisions/source/dependency/Aeneas hashes/full printed axioms in NKH_ATTEMPTS.jsonl and scope receipts. Disk free checked before EACH resumed scope, at least40GB; resumed own writes below40GB. Own cache retained; no shared/sibling/session-A path touched. Only owned uncompressed diagnostic copies may be removed after lossless xz+sha256 verification; NKH_HOST_PACKAGING.json records retention.

Frozen4bb3b3f5crates/programs/Cargo.lock unchanged; no ELF rebuild trigger. Inherited only: default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4; devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299; Pool121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548. No binary/object/ELF/file>20MB committed. No wallet/key/fund/authority action.
'''
(E/'NKH_HANDOFF.md').write_text(text)
d=J('NKH_SCOPE_DISPOSITION.json');d.update(submitted=40,percentage=100,unused=[],historical_stop_preserved='NKH_FAILURE.md / NKH_HOST_FINDING.json',resume='NKH_RESUME.json',complete_receipts=39)
for c in d['candidates']:
 c.update(status='CLOSED',disposition='Admitted by complete NKH combined gate; original domains/caller clauses retained')
 c.pop('why_no_remaining_scope_can_be_attempted',None);c.pop('additional_missing_kernel_roots',None)
(E/'NKH_SCOPE_DISPOSITION.json').write_text(json.dumps(d,indent=1)+'\n')
print('Final handoff and scope disposition written')
