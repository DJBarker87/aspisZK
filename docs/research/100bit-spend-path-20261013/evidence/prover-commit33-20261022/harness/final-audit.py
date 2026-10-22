#!/usr/bin/env python3
"""Check final Lean hashes and accepted axioms; summarize every Rust receipt."""
from pathlib import Path
import json,hashlib,re,subprocess
E=Path(__file__).resolve().parent.parent
root=Path('docs/research/v8-r0-zk-20261009/lean')
records=json.loads((E/'lean/attempts.json').read_text())
final=[]
for mod,a in [('R1Z.ProverCommitTrustedStd24',9044),('R1Z.ProverCommitPublication33',9046),('R1Z.ProverCommitMerge33',9047),('R1Z.ProverCommitSortedStd33',9049),('R1Z.ProverCommitPublicImage33',9050),('R1Z.ProverCommitMapProgram24',9051),('R1Z.ProverCommit33Audit',9052)]:
 r=next(r for r in records if r['attempt']==a)
 assert r['exit_status']==['0'],r
 p=root/(mod.replace('.','/')+'.lean')
 assert hashlib.sha256(p.read_bytes()).hexdigest()==r['source_sha256']
 assert r['print_axioms'] and all('sorryAx' not in l for l in r['print_axioms'])
 for line in r['print_axioms']:
  names=re.search(r'\[(.*)\]',line)[1].split(', ')
  assert set(names)<={'propext','Classical.choice','Quot.sound'},line
 final.append(dict(module=mod,attempt=a,source_sha256=r['source_sha256']))
(E/'final-proof-audit.json').write_text(json.dumps(final,indent=2)+'\n')
rr=[]
for p in sorted((E/'receipts').glob('*/receipt.json')):
 r=json.loads(p.read_text());name=p.parent.name
 pin=E/'pins'/(name+'-inputs.json')
 r.update(name=name,inputs=json.loads(pin.read_text()) if pin.exists() else None)
 r['outcome']='accepted' if r['exit_status']==0 else 'not accepted'
 r['proof_scope']='Bounded Kani loop/transition check with a sorted-association-list std substitute and explicit callee substitutes. Not a general source-to-model refinement.'
 rr.append(r)
(E/'rust-receipts.jsonl').write_text(''.join(json.dumps(r,sort_keys=True)+'\n' for r in rr))
assert not subprocess.check_output(['git','diff','e4fa76dc1','--name-only','--','crates/','programs/'])
print(json.dumps(dict(lean_modules=len(final),rust_finished=len(rr),rust_accepted=[r['name'] for r in rr if r['outcome']=='accepted'])))
