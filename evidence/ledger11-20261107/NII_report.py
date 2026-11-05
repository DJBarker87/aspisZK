from pathlib import Path
import json,lzma,hashlib,subprocess
E=Path(__file__).resolve().parent;J=lambda n:json.loads((E/n).read_text())
m=J('NII_METRICS.json');scan=J('NII_SCAN.json')['diagnostic'];a=J('NII_AUDIT.json');export=J('NII_EXPORT.json');end=J('NII_HOST_END.json');seed=json.loads(lzma.decompress((E/'NII_CACHE_IMPORTS.json.xz').read_bytes()));cp=json.loads(lzma.decompress((E/'NII_CLOSURE_PINS.json.xz').read_bytes()))
commits=subprocess.check_output(['git','log','--oneline','-3'],text=True).strip()
s=f'''# Ledger11 final handoff

**Target not yet established. Fourth all-slices composition FAILS on an owner conflict.**
Branch codex/cx-ledger11-20261107. Local commits only; no push/merge, shipped source, new theorem, Kani, extraction, wallet/key/funds operation or sibling worktree access.

## Ledger and precise finding

All nine unchanged verifier-delta/Pool validators PASS under the private evidence sandbox, with extra checks only. NII_REPLAY_*.json, pinned inputs and NII_VALIDATOR_PROVENANCE.json preserve the runs. The requested393 CLOSED/206 OPEN source-validator count is reproduced exactly:58 new verifier occurrences, no overlap, immutable599-row graph/body/source basis. No support-only or running sibling claim earns row credit. Pool helpers are outside599.

NII_L001 requested unmodified combined import exits1: instDiscriminantVerifierErrorIsize is owned by both NFW_ErrorReferenceTypes and NGL_MapReference.Types. NII_L002 is a DIFFERENT minimal two-import target and reproduces the same failure. No unchanged full import rerun, forest repair, declaration rename or weakening. NII_CONFLICTS.json pins both source/object owners and all importing paths. NHJ_COMBINED_IMPORT introduces the NGL owner through NHJ_SnapshotAssociation/NGL_MetaReferenceModel/NGL_ErrorCarrier; canonical NFW_STAGE2_IMPORT/NGN, and NHS/NHZ/NHW/NIF consumers, reach the NFW owner.

Headline-coherence ledger:379 CLOSED/14 QUALIFIED/206 OPEN. S97/97,Q161/161,D125 CLOSED/14 QUALIFIED/206 OPEN of345. TX1:216/5/132 of353; TX2:163/9/74 of246. Qualification is conservatively at the REQUIRED UNMODIFIED NHJ FOREST gate. Only TX2:223 and TX2:236 packet roots directly depend on the colliding owner; the other12 proofs are not refuted and are independently audited. All14 source-validator credits remain visible. NII_LEDGER/ROUTES/COUNT_RECONCILIATION retain both counts and exact membership. Five TOOL-BOUNDARY rows036/040/041/043/044 remain OPEN. CM31::inv_with covers only deployed M31::inv under(al).

## Audits: explicit diagnostic separation

The requested NII_COMBINED_IMPORT.lean is retained FAILED. NII_DIAGNOSTIC_IMPORT is a separately named PARTIAL environment containing every requested forest except NHJ; NHJ roots are loaded separately by the SAME compiled proof auditor. Neither is substituted for the full gate. NII_AUDIT.json reports FULL_COMPOSITION_FAILED_OWNER_CONFLICT, and NII_SCAN.json reports FULL_GATE_BLOCKED_OWNER_CONFLICT with no invented full-scanner exit0.

Diagnostic raw ax2: {a['diagnostic_root_count']} unique selected roots, standard axioms only; all eight planted/mutation fixtures reproduce exact expected results and collectAxioms agreement in the SAME binary. Canonical NEP walker bytes and compiled pins are unchanged; full driver diffs are committed. NII_L035 retains exit1 for known NHC_DecodeModel.decoder_error raw/summary discrepancy under(ab')(3): raw propext/Classical.choice/Quot.sound, summary empty. No verdict is rewritten.

PARTIAL scanner NII_L009 exits0: {scan['modules']} modules, {scan['declarations']} declarations, {scan['edges']} references; zero dangling/incompatible-owner/import defects; {scan['compatible_cached_replicas']} compatible replicas disclosed. This does not certify the failed combined environment.

## Honest plan and runtime status

NII_STATEMENT.md: four PROVED plan transports ORACLE/HISTORY/CARRIERS/TRANSCRIPT; three PROVED-conditional MODEL theorems DRIVER/EXPERIMENT/POOL.read_to_settlement; TX1 writer established only under retained whole-source extraction; POOL.prefix_to_cpi and L159.physical_instance OPEN. NII_L040 prints all ten exact theorem/headline statements and standard axioms; full quotations in NII_STATEMENTS.md. No native-observer hypothesis or extraction premise is removed. NIF local fields/effect domains do not instantiate the physical twelve-kind NFS producer; verify_observed/op9, TX2 slots, pair/finish and production Pool remain open.

NII_SHORTEST_PATHS recomputes unchanged TX1 six-row and TX2 seven-row OPEN paths. Every spine row names NHY entry, NIH verify_observed/op9, NID TX2, NIG pair/finish or NIE Pool and its last committed obligation. Snapshots are immutable Git objects in NII_READONLY_PROVENANCE.json, never sibling worktree reads. Newer claimed rows, including NIG filled045 and NHY helper candidates, are NOT adopted here.

Pool outside599: A(af) reclassification; supported_loader, height guard, error conversion helpers CLOSED; B and production D OPEN. K086 is a retained abort/liveness finding; actual production reachability/exclusion remains UNPROVED at the three classifier callers and post-System-CPI state. NII_REMAINING lists all dispatch/master/checkpoint/lane/list/marker/custody/registry/metas/CPI/return-register/settlement obligations.

All four lead-added trust rows are inventoried with direct/transitive/OPEN use sites: RuntimeClockSlotBinding, RuntimeReturnDataClear, ReviewedTranscription-prepared_claim and ReviewedTranscription-queries_from_pairs. Nonempty RuntimeReturnData1..1024(ASR8=792) and RuntimeMemcmp ACCEPTED. RuntimeCpiReadonlyEntry7 PENDING/unused. NIB-P1/P2 (and P3/P4) and NHY/NHD candidates are SOURCE REALIZATION obligations, not trust. P6/D188 option-A semantic transport and polynomial transcription are retained RECLASSIFICATION, never removal. SDK/std/allocator/Drop/ABI/compiler/Aeneas/source-to-ELF, RuntimePersistence,SHA256=H and original cryptographic assumptions remain.

Owner(aj)(a) still chooses L159 physical reporting boundary: recommended SAME-game Pool B/D settlement route versus conditional external Pool association. No alternative is silently adopted. Adaptive reorder beyond ARX/F3S requires owner coupling/frozen3 decision. L187 cold coherent release replay and L188 final trust/axiom/native/source-to-ELF audit remain OPEN. Frozen3,L154 parameter,op43/op44,100-bit PER-ATTEMPT/privacy/two transactions remain unchanged.

## Resources, preservation, next deliverable

40/40 slots consumed: {m['by_kind']};37 exit0; failures NII_L001/L002 owner imports and NII_L035 known raw/summary discrepancy. Scope wall sum{m['scope_wall_sum_seconds']:.6f}s; peakRSS{m['peak_rss_kib']}KiB; swaps0. Every attempt records exact target/argv/revision/source/dependency/tool/Aeneas hashes/exit/wall/RSS/swap/axioms. Admission exit0 AND allowed:true; ONE scope at a time,6G/8G/Swap0/Tasks64,Lean-M7000,optimized links. No timeout,memory kill,cap raise or unchanged resource-failure retry. Own preflight/seed/parser repairs are fully retained; no shared infrastructure changed.

Seed:{seed['paths']} paths,{seed['logical_bytes']} logical bytes,{seed['external_copy_bytes']} external-copy bytes; owned-cache hardlinks retain original objects without another corpus copy. Supplements are separately hash-pinned. Own cache {export['cache_retained']} RETAINED. Restore NII_exports_20261107 FIRST, then NII_flat/coherent SInt2/Lean4.32. Four own objects:{export['bytes']} bytes. Requested full import object absent, as expected. Closure manifest pins{len(cp['selected_objects'])} selected object/sidecar files, including actual Aeneas libraries; isolated NHJ static closure is labelled separately from partial scanned modules.

Hash-verified own workspace cleanup removed{end['removed_bytes']} rebuildable bytes after retention; cache never deleted, no active own prover, host free{end['disk_free_bytes']} bytes. No cache/key/predecessor/sibling tree removed. Large pinned inputs stored once by SHA; no file over20MB, binary/object/ELF or Python bytecode committed. Raw evidence whitespace is preserved to retain exact source hashes; authored sources are checked separately.

Frozen source4bb3b3f51e16b4525f1d10336e2b0bcbbd775387 crates/programs/lock tree-identical. No ELF rebuild trigger. INHERITED ONLY: default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4; devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299; Pool121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.

Next: owner/module producers repair the actual forest ownership in a separately authorized job, then replay the complete unmodified selected forest. Independently continue actual entry/op9/TX2/pair/Pool source producers, preserving caller domains and existing trust; then L187/L188. **Target not yet established.**

Stage commits visible at report generation:
```
{commits}
```
'''
(E/'NII_HANDOFF.md').write_text(s)
