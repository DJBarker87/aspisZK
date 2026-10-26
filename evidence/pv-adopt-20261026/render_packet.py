#!/usr/bin/env python3
"""Render adoption documentation from the pinned, Git-only audit outputs."""
import json,pathlib
P=pathlib.Path(__file__).resolve().parent
load=lambda n:json.loads((P/n).read_text())
r=load('revisions.json');c=load('closure.json');merges=load('merges.json');rows=load('recount2-rows.json');d=load('research-drift.json');net=load('candidate-research-net-difference.json');support=load('support-closure.json')
path=P.parents[1]/'design/PV-ADOPT-20261026.md';s=path.read_text()
def section(title,body,next_title):
 global s
 start=s.index('## '+title);end=s.index('## '+next_title,start)
 s=s[:start]+'## '+title+'\n\n'+body.strip()+'\n\n'+s[end:]
table='| Sibling | Pinned head | Exit | Conflicting paths |\n|---|---|---:|---|\n'
for m in merges[:-1]:table+=f"| `{m['ref']}` | `{m['head'][:12]}` | {m['exit']} | "+(', '.join('`'+x+'`' for x in m['conflicting_paths']) or 'none')+' |\n'
section('Sibling merge plan',table+'''
[merges.json](../evidence/pv-adopt-20261026/merges.json) retains the exact `git merge-tree --write-tree --name-only <candidate SHA> <sibling SHA>` argv, exit status, result tree, conflicting paths and diagnostics. These create only Git objects; no branch or worktree was merged. Four sibling dry-runs exit 0; dictionary exits 1 with one content conflict. No PV_CB_/PV_CB3_/PV_RunJoin_/PDict_ Lean path conflicts.

The dictionary conflict is `tools/prover-rw-20261023/native-drop/run-joint.sh:21`, the private historical launcher's attempt-range case. Candidate accepts 12400–13199; dictionary instead carries 12000–12399 and 14400–14799 (both also carry the earlier shared alternatives). Proposed resolution on the eventual integration branch: retain the union of these historical accepted ranges, changing only that case line. This is a review proposal, not permission to edit any shared host launcher. The actual replay uses the lead-managed env-J range and standing 128-task setting; it must not use this historical private script. There is no reason to drop either side's proof sources or receipts to resolve the launcher metadata.

Recommended order on a **new integration branch**, after gate closure and lead authorization: (1) pv-rebase (the measured research merge/evidence baseline); (2) refresh with the pinned research snapshot, preserving the selected64 client route; (3) dictionary, with the explicit one-line conflict resolution above; (4) cb; (5) cb3; (6) runjoin. Source-identification modules arrive with research; subsequent srcid/rw continuations require new pins and another dry-run. Install the common selector and concrete native/world instance after those sources coexist. Re-run `merge-tree` against the accumulated integration head before each actual merge; pairwise clean results do not certify the combined union. Do not merge into research until the security/deployment gates and final source binding pass.

[declarations.json](../evidence/pv-adopt-20261026/declarations.json) records the column-zero `theorem`, `def`, `structure` inventory (also common modifiers), with lexical fully qualified namespaces, source module and line, across candidate and all five siblings, including generated ProverRwFull modules. **Zero cross-file public fully-qualified-name collisions**. 2,603 public names recur across histories at the same module path; these are inherited declarations, not duplicate declarations to concatenate. Private declarations are excluded from public-name collisions. This is the requested grep/namespace audit, not Lean elaboration or a guarantee about future generated declarations.
''','Research drift')
section('Research drift',f'''Pinned research: `{r['research']}`. Current research into candidate dry-run: **exit 0; zero conflicts**. The measured baseline `3f9177b647` contains research control `326bdc375b0a426d2fd4b9324ed27f29ecb05bec`.

**New research paths under crates/ or programs/: {d['count']}.** Both `git log --format=%H 3f9177b647..{r['research']} -- crates programs` and the control-to-research content diff are empty. [research-drift.json](../evidence/pv-adopt-20261026/research-drift.json) records both tests. There is therefore no new research source path requiring a three-ELF rebuild at this snapshot. This does not establish the final candidate's source/effect refinement or final release binding.

The literal two-tree `git diff --name-status --no-renames 3f9177b647 {r['research']} -- crates programs` lists **25** paths, all under crates/, zero under programs/. These are the existing candidate-only rewrite/feature/harness differences viewed in reverse, not research development after the control. They were already present in the measured candidate-versus-control gate. The per-path inventory is [candidate-research-net-difference.json](../evidence/pv-adopt-20261026/candidate-research-net-difference.json). Any **new edit** to any of these paths, or any other crates/programs path, invalidates historical ELF-pin evidence for that new source: rebuild default, devnet and Pool and confirm all three pins, or stop and escalate. No rebuild is performed here.

| Existing baseline difference path | Consequence of a new edit before adoption |\n|---|---|\n'''+''.join(f"| `{x['path']}` | Rebuild and confirm all three ELF pins. |\n" for x in net['paths'])+'''
Before adoption, compare the final integrated source against the measured candidate as well as research. Historical byte identity is reusable only with an exact unchanged-source/feature/toolchain association or a newly admitted rebuild; this packet makes no automatic promotion of old receipts.
''','Privacy closure and remaining joins')
cbmods=sorted({i['module'] for i in c['inventory'] if i['module'].startswith('R1Z.PV_CB_Op') and i['module'].endswith('Source')}|{'R1Z.PV_CB_TakeSource'})
rowmap=[x for x in rows if 'R1Z.PV_CB_' in str(x.get('theorem'))]
(P/'callback-row-map.json').write_text(json.dumps(dict(recount2_rows=rowmap,current_source_modules=cbmods,note='Recount 2 credits 23 CB rows including TakeSource/op3; current sibling also contains Op229Source (op229/V246). D211 says 24 but enumerates only 23 row IDs. Do not silently add closure credit.'),indent=2)+'\n')
section('Privacy closure and remaining joins',f'''The starting declaration is `R1Z.PrivacyR1HeadlineDeployedReal.privacy_headline_deployed`, source lines 80–159. Its module imports `R1Z.ProverCommitDeployedFuel22`; its explicit `RustRealRefinement` hypothesis (lines 69–78) supplies a `ProverCommitFuelJoin22.RunJoin` for the **complete view plus observer decision**, outside the fixed parser/seed/fuel bad event. The theorem calls the admitted model headline, owned caller law and the coupling test bound. It does **not** construct the deployed caller from the rewrite.

The Git-source DAG has **{len(c['topological_modules'])} resolved local modules**; every directed import edge, deterministic dependency-first list and external import boundary is in [closure.json](../evidence/pv-adopt-20261026/closure.json). [headline-sources.json](../evidence/pv-adopt-20261026/headline-sources.json) binds module paths, source hashes and revisions. Resolution includes the v8-r0-zk, v8-r0-sem-proof, v8-full-view-zk and 100bit lean roots; generated `lean/prover-rw-20261023/ProverRwFull*.lean` are mounted as `R1Z.ProverRwFull*` as in their imports. External Aeneas/mathlib/remaining extraction objects must be pinned through env J, not rebuilt as a cold package build.

There is **no import path** from the headline to `R1Z.ProverRwP6BodyData`, any ProverRw-family module, any PDict_ module, or any PV_ module. `ProverRwFull` is a **namespace**, not an importable `R1Z.ProverRwFull` module: the actual extracted modules are `R1Z.ProverRwFullTypes`, `ProverRwFullExternalTypes`, `ProverRwFullExternalFuns`, `ProverRwFullFuns`. Their namespace is global `ProverRwFull`. The separate P6 source chain starts `ProverRwP6BodyData → ProverRwP6BodyGamma / ProverRwBodyCandidateData`; `refinement_of_data` keeps the whole proof/audit `data ... = model` hypothesis. Even a successful P6 compilation does not supply that equation or native execution association.

A convenient schematic of the actual gap is:

```text
PrivacyR1HeadlineDeployedReal → ProverCommitDeployedFuel22 → model/caller/coupling DAG
    RustRealRefinement supplied as a hypothesis
    [NO import/application edge to the source components below]
ProverRwP6BodyData → P6 selector/body data criterion → extracted ProverRwFullFuns
PV_CB_ / PV_CB3_ source laws       PDict_ selected operation/carrier installs
PV_RunJoin_Endpoint conditional runtime/world certificate
PV_Src_ identification / BuilderPremises consumers
```

**Unimported sibling-family modules: {len(c['unimported_sibling_modules'])} distinct modules** across the five requested sibling snapshots (PV_334, PDict_305, ProverRw351). Of those, **{len(c['unimported_sibling_additions'])}** are absent from the candidate tree. Prefix-specific counts: PV_CB_122, PV_CB3_13, PV_RunJoin_139, PDict_305; the remaining modules are other PV_/ProverRw source support. The broader pinned union including research is {c['unimported_count']} unimported family modules, including **{len(c['research_source_identification'])} PV_Src_ modules on research**. Counts are module inventories, not independent proof obligations or claims that every exploratory/audit module must be imported. Exact lists and per-branch membership are in closure.json.

| Component absent from headline route | Exact recount-2 rows / remaining join |
|---|---|
| CB source laws | V169; V197–V199; V202–V206; V208–V216; V218; V223–V224; V226–V227 are CLOSED-ON-CANDIDATE **source equations**. Install them into the **same** ExternalFuns selector used by the P6/native caller; prove transport and effect adequacy under V165–V167, then consume that caller in V038. |
| PDict installs | V200/op78 and V248/op231 are CLOSED-ON-CANDIDATE; `PDict_RemainingDictionary231` supplies them. Common selector compatibility, native carrier/File/world laws (V268/V269/V271), feature/ABI/effect transport V165–V167 remain. Never add overlapping callback counts across siblings. |
| rw body/data | V163 whole data and V164 original-helper correspondence remain OPEN in recount 2; later rw17/rw18 component results do not install a concrete model instance. V255/op247 and V262/op255 already have scoped source credit. Connect full Result, proof/audit bytes, reservation, retry and cleanup effects. |
| PV_RunJoin_Endpoint | V036/V037 marginals and V038 agreement stay on the SAME coupling. V045 concrete rust/runtime and its boundary remain parameters; the endpoint exposes eight fields, not eight discharges. Join source_V045, E1_V329, native_fill_V336, native_ledger_V337 and the remaining complete-view/kernel/observer obligations for the selected native route. E1/E2 remain literal native laws. |
| PV_Src_ | Recount-2 V152/V153/V154 OPEN; D213 later reduces them to compile_call, words, publicCorr, admission, row_call families. Consume `PV_Src_NativeIdentification` through BuilderPremises with the **actual selected input and installed transport**; do not infer native fixture inhabitance from mathematical fibres V047. D214's raw-mapper counterexample is retained. |
| L1/L2/L3 | V347–V351, V352–V369, V366 shared trace coupling and V380-inversion need actual seed/oracle/retry/error/cleanup association; isolated erasures do not suffice. L3 V370–V374, client V396 and replay/binding V397–V399 stay separately accountable. |

[callback-row-map.json](../evidence/pv-adopt-20261026/callback-row-map.json) lists every currently present CB source module: **24** ({len(cbmods)-1} Op*Source modules plus TakeSource). Recount 2 credits **23** CB rows (including TakeSource); D211 calls these “24” but its enumerated row IDs total 23. The current sibling additionally contains Op229Source/op229 (V246); it has no retroactive recount-2 credit. Merely adding imports would enlarge the module DAG, but only applying the laws in the concrete endpoint certificate removes premises. No import-only closure is claimed.

[recount2-rows.json](../evidence/pv-adopt-20261026/recount2-rows.json), pinned from research, is the exact per-row authority. D211's recount totals are 403 rows, OPEN110 / REDUCED154 / EVIDENCED12 / CLOSED-ON-RESEARCH87 / CLOSED-ON-CANDIDATE40. D216 subsequently supplies timing evidence; it does not close the remaining security rows.
''','Final replay plan — proposed, not executed')
path.write_text(s)
