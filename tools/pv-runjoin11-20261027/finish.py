#!/usr/bin/env python3
import hashlib,json,pathlib,subprocess
root=pathlib.Path(__file__).resolve().parents[2];e=root/'evidence/pv-runjoin11-20261027';base='623a1d3be6'
subprocess.run(['python3',str(root/'tools/pv-runjoin11-20261027/tally.py')],check=True)
pre=json.loads((root/'evidence/pv-runjoin10-20261027/P-before-after.json').read_text())
pre['entry_revision']=subprocess.check_output(['git','rev-parse',base],cwd=root,text=True).strip()
pre['new_source_results']=['Literal recorded public/transition data from ed1c1cef71 fixture bytes, typechecked. No source decoder or returned-compilation association proved.','Unstubbed optimized Kani root source cells 18/19 passed; combined historical coverage 21/21.']
pre['exact_deployment_statements_file']='stage1-missing-fact.md';pre['runtime_checklist']='stage2-missing-fact.md'
pre['fixtures']={v:{'selected_record_term':None,'recorded_public_term':'R1Z.PV_RunJoin_Recorded'+v.title()+'.publicRecord','recorded_transition_term':'R1Z.PV_RunJoin_Recorded'+v.title()+'.transition','compiler_return':'OPEN','public_binding':'OPEN','non_vacuity':'P ∧ T OPEN; T hypothetical'} for v in ['transfer','withdrawal']}
(e/'P-before-after.json').write_text(json.dumps(pre,indent=2)+'\n')
paths=['docs/research/v8-r0-zk-20261009/lean/R1Z/'+n+'.lean' for n in ['PV_RunJoin_TrustEndpoint','PV_RunJoin_TrustItems','PV_RunJoin_JoinedCausalHeadline','PV_RunJoin_Deployed','PV_RunJoin_Boundary','PrivacyR1HeadlineDeployedReal']]
records=[]
for path in paths:
 p=root/path
 if not p.exists():continue
 old=subprocess.check_output(['git','show',base+':'+path],cwd=root);b=p.read_bytes();records.append(dict(path=path,sha256=hashlib.sha256(b).hexdigest(),unchanged_from_entry=old==b))
lean=list((root/'docs/research/v8-r0-zk-20261009/lean/R1Z').glob('PV_RunJoin_*11*.lean'))+[root/'docs/research/v8-r0-zk-20261009/lean/R1Z'/('PV_RunJoin_Recorded'+v+'.lean') for v in ['Transfer','Withdrawal']]
for p in lean:
 t=p.read_text();assert not __import__('re').search(r'\b(sorry|admit|native_decide|implemented_by|axiom)\b',t)
(e/'final-source-audit.json').write_text(json.dumps(dict(original_endpoints=records,new_sources=[dict(path=str(p.relative_to(root)),sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in lean],source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),release_claim=False),indent=2)+'\n')
(e/'COMMITS.txt').write_text(subprocess.check_output(['git','log','--oneline',base+'..HEAD'],cwd=root,text=True))
rows=[json.loads(p.read_text()) for p in sorted(e.glob('receipt-*.json'))];ks=[json.loads(p.read_text()) for p in sorted(e.glob('pv11-runjoin-kani-*/receipt.json'))]
table='| ID | Target | Exit | Wall s | Peak RSS bytes | Swap |\n|---:|---|---:|---:|---:|---:|\n'+'\n'.join(f"| {r['attempt']} | {r['target']} | {r['exit']} | {r.get('wall_seconds')} | {r.get('peak_rss_bytes')} | {r.get('swaps')} |" for r in rows)
report=f'''# pv-runjoin11 — exact source-leaf obstruction

**Target not yet established. Requested selected-record deliverable remains incomplete.**
Branch `codex/pv-runjoin-20261026`; entry `{base}`. No push.

Both fixtures still have **no actual selected-record Lean term**, no compiler-return
equation, no deployed source public binding, and no P ∧ T non-vacuity proof.
`PV_RunJoin_RecordedTransfer` and `PV_RunJoin_RecordedWithdrawal` provide only
literal publicRecord/transition/publicInput data from the pinned 1880-byte terminal
fixtures at ed1c1cef71. The generator passed --check. This is byte-field extraction
plus carrier typechecking, not a theorem about the Rust decoder or compiler return.
There is no arbitrary compiled parameter presented as actual deployed data.

The exact missing mapper proposition for each fixture and its shipped locations
are recorded in stage1-missing-fact.md and stage2-missing-fact.md. The shipped
records leaf remains a class parameter in the port; the owned dynamic dictionary
has not been identified with that leaf. Stop each stage there under the explicit
missing-fact instruction; no new conditional bridges were proved around it.
Runtime/observer installation and stage 4 were not started. The source facts are
not ROW counterexamples. No full manifest or coherent release replay is claimed.

Constructed P **{{source public binding, trace}} → {{source public binding, trace}}**;
deployed P unchanged and OPEN. Endpoint rows removed/added/weakened: **0/0/0**.
Record counts **2/8/6 → 2/8/6**. T unchanged: entropy_law, entropy_kernel,
observation; T hypothetical; A/B unadopted. Exact prior before/after statements
are retained in P-before-after.json with fixture status. Original endpoint sources
are unchanged (final-source-audit.json).

Source root cells 18 and 19 passed with the unchanged optimized Kani configuration,
no stubs; combined historical coverage **19/21 → 21/21**. These checks do not
prove a mapper equality, compiler success, source public binding, or L2 trace.
The original 25 missing objects remain restored; the remaining 11 L2 objects
were not attempted.

Validation: **{len(rows)}/100 Lean attempts**, {sum(r['accepted'] for r in rows)} accepted;
**{len(ks)}/4 Kani runs**, {sum(r['exit']==0 for r in ks)} successful. IDs
40300–{rows[-1]['attempt'] if rows else 40300} used once, next {rows[-1]['attempt']+1 if rows else 40300};
no reservation refusals. Last three actual Lean attempts are the focused trust
audit. All axiom reports are subsets of [propext, Classical.choice, Quot.sound].
Every receipt includes exact target, exit, wall, peak RSS, swap, revision, source
snapshot/hash, dependency fingerprint, full axiom output and caps. Kani axioms N/A.
Shared launcher TasksMax=128 under lead ruling (b); own Kani scopes TasksMax=64.
All runs had swap zero. Raw receipts/logs and receipt-index.tsv are retained.

{table}

**Allocation is not exhausted:** {100-len(rows)} Lean attempts and {4-len(ks)} Kani
runs remain. This is an explicit missing-fact stage stop, not an exhaustion claim
or a claim to have fulfilled the whole-budget instruction. Dependent stages
remain gated; spending the rest on more bridges would violate the requested
focus. The target and requested main deliverable remain unestablished.

Next deliverable: identify the shipped Records leaf at the same transfer fixture
arguments, then construct the actual selected Input and prove its compiler-return
and equality to RecordedTransfer.transition; repeat for withdrawal before installing
runtime/observer and proving P ∧ T non-vacuity.

Only the pre-existing cfg(kani) child gained the two harnesses; no production body,
ELF pin, simulator, observer, wallet or key changed. Final build cache cleanup is
recorded separately. Commits are in COMMITS.txt.
'''
(e/'REPORT.md').write_text(report)
print(json.dumps(dict(lean=len(rows),kani=len(ks),report=str(e/'REPORT.md'))))
