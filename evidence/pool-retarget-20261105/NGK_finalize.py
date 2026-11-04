"""Final additive gate and handoff; no prover launch, push or row promotion."""
from pathlib import Path
import json,subprocess,sys,collections,hashlib,lzma
E=Path(__file__).resolve().parent;J=lambda p:json.loads(p.read_text())
for name in ['NGK_collect.py','NGK_validate.py','NGK_tests.py']:subprocess.run([sys.executable,str(E/name)],check=True)
rows=[json.loads(l) for l in (E/'NGK_ATTEMPTS.jsonl').read_text().splitlines()];assert len(rows)==110
counts=dict(collections.Counter(r['kind'] for r in rows));failed=[r['attempt'] for r in rows if r['exit_status']]
assert set(failed)=={'NGK_L022','NGK_L032'}
metrics=dict(attempts=110,budget=110,by_kind=counts,success=108,excluded_failed_elaborations=failed,kani=0,extraction=0,wall_seconds=sum(r['wall_seconds'] for r in rows),peak_rss_kib=max(int(r['peak_rss_kib']) for r in rows),swaps=sum(int(r['swaps']) for r in rows),scope_caps=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64),lean_memory_flag='-M7000',max_own_concurrent_scopes=1,no_timeout_or_memory_kill=True,no_unchanged_timeout_retry=True,no_cap_raise=True,prelaunch_nonattempt='NGK_L001 missing fixture companion, corrected before any Lean process; NGK_PREFLIGHT_FIXES.json')
(E/'NGK_RESOURCES.json').write_text(json.dumps(metrics,indent=1)+'\n')
a=J(E/'NGK_AUDIT.json');a.update(budget=metrics,compiled_proof_modules=[r['target_module'] for r in J(E/'NGK_PROVENANCE.json')['files']],explicit_theorem_associations='NGK_CERT_ASSOCIATIONS.json.xz',source_revision_before_final_commit=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip());(E/'NGK_AUDIT.json').write_text(json.dumps(a,indent=1)+'\n')
p=E/'NGK_REMAINING.md';t=p.read_text();start=t.index('No Pool consumer row becomes CLOSED');t=t[start:]
p.write_text('# NGK remaining obligations\n\nAll selected ownership families are retargeted: GuardBody/S2Sdk, Prepared/PrepQM, Phase, NED/NBN/NBK library and other canonical dependencies are reused read-only; all48 nonreused Pool modules compile. Combined raw audit, same-binary fixtures, full zero-defect scan and all119 explicit statement/owner associations PASS. **No family within the selected proof forest remains unretargeted.**\n\n'+t.replace('This job\'s Lean-only work is complete only when all 48 proof copies, the combined\nimport, complete raw roots, eight same-binary fixtures, full scan and explicit\nstatement/owner associations pass. Family-by-family results are then listed in\nNGK_HANDOFF.md; no separate unretargeted family is silently waived.','This job\'s Lean-only work is complete:110/110 attempts used. All gates listed above pass; no independent Lean-only retarget obligation remains. The remaining B/D obligations require native same-execution caller/domain evidence.'))
(E/'NGK_HANDOFF.md').write_text('''# NGK canonical Pool forest handoff

**Pool forest headline-coherent. B and D OPEN; no Pool consumer row becomes
CLOSED by this job. Target not yet established.** Branch
codex/cx-pool-retarget-20261105; no push, merge, Kani, extraction, shipped-source
change or wallet/key operation.

## Exact claim and evidence

All48 selected NFO/NFR/NFV proof modules replay as NGK-prefixed copies.
NGK_DIAGNOSIS.json enumerates the complete9,506-module legacy closure before
canonical reuse. All ownership families are resolved: RPz7 GuardBody/SDK,
Prepared/PrepQM and canonical Phase; NFN/NFS/NFY/NGE/NGF library chains;
other already-admitted dependencies;48 nonreused Pool copies. No competing shared
owner is redefined. NGK_FAMILIES.md and NGK_DECLARATION_USES.json give exact uses.
NGK_PROVENANCE.json retains source path/hash/range and full before/after bodies
and statements. Only imports and qualified owner/proof names change. Seven
copies require the emitted decoder map_err qualification, paired with the reused
NFY_OwnerTransport.map_err_transport exact full-Result theorem. Nominal old/new
local carriers are consistently retargeted, never cast by an assumed equality.
NGK_prepare.py --check verifies generated proof bytes; NGK_families.py regenerates
the additional diagnosis table. No new axiom or security hypothesis.

NGK_COMBINED_IMPORT.lean loads RPx_Deployed + unchanged NGJ_VERIFIER_IMPORT +
all selected NGK Pool proofs in ONE environment. NGK_AUDIT.json raw-walks4,714
roots (4,167 verifier +547 Pool including generated auxiliaries): standard axioms
only, zero collectAxioms disagreements. Every explicit Pool theorem is included.
All eight planted/mutation fixtures reproduce in the SAME compiled proof binary
as all20 raw batches. Walker bytes equal NEP_WALKER; complete driver diffs are
committed. NGK_SCAN.json covers13,424 modules,689,457 declarations and24,433,563
references: ZERO dangling, incompatible owners or import mismatches;1,583
compatible cached replicas remain disclosed. None of the three conflicting
legacy owners is loaded. Independent import baselines come from committed NGJ
sources and the actual NGK source import lists, never the candidate scan.

NGK_CERTIFICATES.json enumerates320 selected historical/source theorem records
before loaded lookup. NGK_CERT_ASSOCIATIONS.json.xz and the33 disjoint statement
receipts check the full kernel types and exact actual owner of all119 explicit
Pool theorems. All copied top theorems have #print axioms, standard only. These
are model/ownership checks, not a new native implementation bridge.

## Ledger, validators and trust

Seven unchanged NFV validators pass in a private output sandbox; all seven
outputs are BYTE-IDENTICAL to historical outputs (NGK_VALIDATOR_PROVENANCE.json).
NGK_validate.py adds provenance, compiled-source, caps/admission and frozen-body
checks. NGK_TESTS.json rejects14 evidence mutations, plus five source/provenance
mutations in NGK_VALIDATION.json. No historical predicate was waived.
NGK_LEDGER_DELTA.json adds ZERO CLOSED rows. It removes the Pool forest's
ownership/coherence obstruction so NGG's B/D certificates can be admitted AFTER
the same retarget and their native/domain gates; it does not admit them here.
Read-only committed sibling observations are in NGK_SIBLING_STATUS.json.

No assumption discharged, added or removed. Retained: P6/D188 option-A native
semantic transport (RECLASSIFICATION), SDK/std/allocator/ABI/compiler/Aeneas and
source-to-ELF realization, RuntimePersistence, digest/H, accepted nonempty
RuntimeReturnData1..1024 (ASR8=792), RuntimeMemcmp and cryptographic assumptions.
L154 remains a statement parameter; coherent digest/error slots remain op43/op44.
Privacy, two transactions and100-bit PER-ATTEMPT target are unchanged. This is a
focused cached coherent replay, not a cold release replay or deployed-security
claim. Exact remaining B/D native caller/account/borrow/settlement obligations
are in NGK_REMAINING.md; no selected owner family remains unretargeted.

## Resources and restoration

'''+f'''110/110 allocations used: {counts};108 successes and two excluded
elaboration failures (L022/L032), both corrected by the existing exact emitted
helper qualification in L049/L050. No timeout, memory kill, cap raise or unchanged
failed-shape retry. One own scope at a time; every admission exit0 AND allowed:true;
MemoryHigh6G/MemoryMax8G/SwapMax0/TasksMax64, Lean -M7000, optimized -O3 links.
Wall sum {metrics['wall_seconds']:.6f}s; peak RSS {metrics['peak_rss_kib']}KiB;
swaps0. NGK_ATTEMPTS.jsonl and linked receipts retain exact target/argv, revision,
source hashes, direct dependencies/Aeneas pins, exit/wall/RSS/swap and axioms.
One own-input missing-fixture preflight launched no compiler and is recorded.

'''+'''Owned cache /home/dombarker/project-offloads/codex-cx-pool-retarget-cache-20261104
is retained, never deleted. Initial copied/pinned seed:55,552 paths and9,097,502,136
unique bytes; fixtures are separately pinned. Predecessor caches/session A and
sibling worktrees were not edited. NGK_EXPORT.json and NGK_CLOSURE_PINS.json.xz
record retained own exports and actually resolved final objects, including Aeneas.
Restore own NGK_exports_20261105 first, then this owned flat cache, then the
coherent SInt2 workspace/root/objects and pinned Lean toolchain. Do not restore
legacy Pool precedence. NGK_PACK.json preserves repeated large inputs once by
SHA256; no file over20MB or Python bytecode, object, binary, tarball or ELF is
committed. Own rebuildable-workspace cleanup, if performed, is hash-verified in
NGK_HOST_END.json; the cache, sources and evidence remain.

Crates/programs are byte-identical to frozen4bb3b3f51e16b4525f1d10336e2b0bcbbd775387.
No ELF rebuild trigger. INHERITED ONLY, not rebuilt/rehashed by NGK: default
f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4;
devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299;
Pool121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.

Stage commits:4f003279d69 diagnosis/generation; b43541d7f96 focused replay;
7fd461d82aa combined audit/fixtures/scan; subsequent validator/delta and final
handoff commits are recorded in git history. No push. Next deliverable: canonical
NGG production-prefix retarget plus B/D same-execution admission/settlement
association. **Target not yet established.**
''')
print(json.dumps(metrics))
