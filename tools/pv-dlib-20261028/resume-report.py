"""Summarize actual receipts/statuses without promoting drafts or finite tests."""
from pathlib import Path
import json,hashlib,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-dlib-20261028'
rows=[json.loads((E/r/'status.json').read_text()) for r in ['V187','V201','V231','V234','V235','V236','V237','V238']]
t=json.loads((E/'TALLY.json').read_text());receipts=[]
for p in sorted(E.glob('*/receipt.json')):
 j=json.loads(p.read_text());receipts.append(dict(path=str(p.relative_to(E)),**j))
(E/'rows-after.json').write_text(json.dumps(rows,indent=2)+'\n')
(E/'receipts-index.json').write_text(json.dumps(receipts,indent=2)+'\n')
revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
log=subprocess.check_output(['git','log','--oneline','b3ad0edf5b..HEAD'],text=True)
(E/'commits.log').write_text(log)
passed={}
for j in receipts:
 m=j.get('module')
 if m and j.get('exit')==0:
  p=R/j['source_path']
  if p.exists() and hashlib.sha256(p.read_bytes()).hexdigest()==j['source_sha256']:passed[m]=j
root=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
drafts=[]
for p in sorted(root.glob('PV_DL_*.lean')):
 m='R1Z/'+p.stem
 if m not in passed:drafts.append(dict(module=m,path=str(p.relative_to(R)),sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
(E/'uncompiled-drafts.json').write_text(json.dumps(drafts,indent=2)+'\n')
closed=[r['row'] for r in rows if r['residual_removed']]
lines=['PV_DL D349 RESUME REPORT','Worktree EXACTLY '+str(R),'Branch '+subprocess.check_output(['git','branch','--show-current'],text=True).strip(),'Revision '+revision,'Resume base c2f6692c0ac48ff53accd2275117768f43b1eb89','',f'Native candidate links supplied: {len(closed)}/8: '+', '.join(closed),
 'Lead recount acceptance is not inferred. Target not yet established.',
 'Whole deployed headline premises removed:0. Native/compiler/caller integration, real RunJoin, E1/E2 and L1/L2/L3 remain.',
 'Trust fields added:0; T stays entropy_law, entropy_kernel, observation. Observer/simulator unchanged. V232 untouched.','',
 'PER ROW (all before/after statements, guards and scope in V*/status.json and native-link.json)']
for r in rows:
 lines += [r['row']+': '+r['status'],'  closing theorem: '+str(r['closing_theorem']),'  evidence class: '+r['native_evidence_class'],'  residual before: '+str(r['before_residual'])+'; after: '+str(r['after_residual'])]
lines += ['',f'Fresh budget:100 Lean /0 Kani; IDs43400–43499 only; usedIDs={len(t["used_ids"])}; chargedLean={len(t["lean_charged"])}; refusedIDs={len(t["used_ids"])-len(t["lean_charged"])}.',
 'No Kani verification run in the resume. RUSTFLAGS --cfg kani in native cargo test only enables the private snapshot accessors; it does not invoke cargo-kani/CBMC.',
 'Old copy-dependent Kani PASS credit stays suspended. Structural K-1 substitutes await re-verification with the lead-validated remedy when budget is authorized.',
 'All5673 authoritative and selected external objects matched before first compile; private existing caches reused, no external rebuild/substitution.',
 'Every actual host receipt: receipts-index.json (target,exit,wall,peakRSS,swap,revision,print_axioms). Caps6G/8G/swap0/Tasks64; Lean-M7000. Failed candidates/source snapshots retained, not credited.',
 'Final audit/replay and closure fingerprint: see successful current-source receipt entries and resume-final-closure-fingerprint.json; do not infer success for missing receipts.',
 'Uncompiled drafts are explicitly listed in uncompiled-drafts.json; no draft credited.',
 '', 'PROCESS DEVIATION',
 'Staging admission04:42:54.960463Z was167.062062s after43441 refusal04:40:07.898401Z (12.938s early). It refused; no upload/compiler ran.',
 'Recorded in PLAN.md. Replacement local input guard enforces180s after receipt of each refusal across all used admission paths; pre-admission hold does not consume an ID. See COOLDOWN.json and cooldown-history.jsonl. Shared host infrastructure/caps unchanged.',
 '', 'No production crates/programs, wallet/account keys, shared sources, other worktrees or release ELFs changed.',
 'Stop reason and next deliverable must be supplied by the final handoff after reviewing the actual current receipts.']
(E/'REPORT.txt').write_text('\n'.join(lines)+'\n')
print('report:',len(closed),'candidate links;',len(t['lean_charged']),'charged Lean;',len(drafts),'uncompiled drafts')
