#!/usr/bin/env python3
from pathlib import Path
import json,hashlib,re,subprocess
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s7-kani2-20261021'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
manifest=json.loads((E/'manifest.json').read_text());accepted={}
for r in manifest['attempts']:
 if r.get('module') and r['exit_status']==0:
  accepted.setdefault(r['module'],[]).append(r)
proofs=[]
for p in sorted((B/'lean').glob('S7Kani2*.lean')):
 matches=[r for r in accepted.get(p.stem,[]) if r['source_sha256']==sha(p)]
 assert matches,p
 r=matches[-1];declared=len(re.findall(r'^theorem\s+',p.read_text(),re.M))
 assert len(r['print_axioms'])==declared,(p,declared,r['print_axioms'])
 for line in r['print_axioms']:
  assert 'sorryAx' not in line
  if 'depends on axioms:' in line:
   axioms=line.split('depends on axioms:')[1].strip().strip('[]').split(',')
   assert all(a.strip() in ['propext','Classical.choice','Quot.sound'] for a in axioms),line
 proofs.append(dict(module=p.stem,sha256=sha(p),attempt=r['receipt'],exit=r['exit_status'],wall_seconds=r['wall_seconds'],peak_rss_bytes=r['peak_rss_bytes'],swaps=r['swaps'],print_axioms=r['print_axioms']))
subprocess.check_call(['git','diff','--exit-code','ae0544388','--','crates','programs'],cwd=R)
changes=subprocess.check_output(['git','diff','--name-status','ae0544388','--',str(B/'lean')],cwd=R,text=True).splitlines()
assert all(l.startswith('A\t') for l in changes),changes
newmodules=[str(p.relative_to(R)) for p in sorted((B/'lean').glob('S7Kani2*.lean'))]
out=dict(schema='focused-extractor-proof-packet-v1',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),new_modules=newmodules,accepted_current_lean=proofs,new_theorem_audits=sum(len(p['print_axioms']) for p in proofs),peak_lean_rss_bytes=max(p['peak_rss_bytes'] for p in proofs),swaps=sum(p['swaps'] for p in proofs),shipped_changes=[],existing_lean_module_edits=[],endpoint_changed=False,full_manifest_replay=False,reason_no_full_release_replay='Incomplete source/backend/caller joins; focused local proof packet only. No unchanged full regression repeated.',status='PARTIAL; S7/R17 not discharged')
(E/'final-audit.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:out[k] for k in ['new_theorem_audits','peak_lean_rss_bytes','swaps','status']}))
