#!/usr/bin/env python3
"""Audit pinned focused evidence; never rerun an unchanged Lean target."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

root=Path(__file__).resolve().parents[1]
evidence=root/'r1p-final'
rows=[json.loads(x) for x in (evidence/'history-fresh-attempts-9800-9999.jsonl').read_text().splitlines()]
prior=[]
for p in ('history-attempts-9800-9999.jsonl','history-real-attempts-9800-9999.jsonl'):
 prior += [json.loads(x) for x in (evidence/p).read_text().splitlines()]
assert len({r['attempt'] for r in prior+rows})==len(prior+rows)
assert all(9800<=r['attempt']<=9999 and r['env']=='J' and r['swaps']=='0' for r in rows)
assert len({(r['module'],r['source_sha256'],r['deps_fingerprint']) for r in rows})==len(rows)
finals={r['module']:r for r in rows}
allowed={'propext','Classical.choice','Quot.sound'}
artifacts=[]
audit_count=0
remote='dombarker@100.108.41.90'
j='/home/dombarker/project-offloads/aspis-joint-20261019'
for module,r in sorted(finals.items()):
 p=root/'lean'/(module+'.lean'); s=p.read_text()
 assert r['exit']==0, (module,r['exit'])
 assert hashlib.sha256(p.read_bytes()).hexdigest()==r['source_sha256']
 assert not re.search(r'\b(sorry|admit|native_decide)\b|^\s*axiom\s|set_option\s+(maxRecDepth|maxHeartbeats)',s,re.M)
 audits=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",r['output'])
 no_axioms=re.findall(r"'([^']+)' does not depend on any axioms",r['output'])
 audits += [(name,'') for name in no_axioms]
 assert len(audits)==len(re.findall(r'^theorem ',s,re.M))
 assert len(audits)==len(re.findall(r'^#print axioms ',s,re.M))
 for name,axioms in audits:
  assert set(a.strip() for a in axioms.split(',') if a.strip())<=allowed,(name,axioms)
 audit_count += len(audits)
 deps=[line.split(maxsplit=1)[1] for line in r['dependency_objects']]
 commands=[f'sha256sum {j}/sources/{module}.lean',f'sha256sum {j}/objects/{module}.olean',f'stat -c %s {j}/objects/{module}.olean']
 commands += ['sha256sum '+p for p in deps]
 out=subprocess.check_output(['ssh',remote,'set -e\n'+'\n'.join(commands)],text=True).splitlines()
 assert out[0].split()[0]==r['source_sha256']
 assert out[3:]==r['dependency_objects'],(module,'dependency object changed')
 artifacts.append(dict(module=module,attempt=r['attempt'],source_sha256=r['source_sha256'],
  source_revision=r['source_revision'],deps_fingerprint=r['deps_fingerprint'],dependency_objects=r['dependency_objects'],
  exit=r['exit'],wall=r['wall'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],
  axioms=audits,object_sha256=out[1].split()[0],object_size=int(out[2])))
base='55c62085d'
tracked=subprocess.check_output(['git','ls-tree','-r','--name-only',base,str(root/'lean')],text=True).splitlines()
for name in tracked:
 if name.endswith('.lean'):
  assert Path(name).read_bytes()==subprocess.check_output(['git','show',base+':'+name]),name
subprocess.run(['python3',str(evidence/'build-history-real-endpoint.py'),'--check'],check=True)
report=(evidence/'PRIVACY-HISTORY-FRESH-20261021.md').read_text()
for filename,name in [('PrivacyR1FinalProtocolHistory.lean','privacy_R1_protocol_history'),('PrivacyR1FinalProtocolHistoryReal.lean','privacy_R1_protocol_history_real')]:
 s=(root/'lean/R1Z'/filename).read_text(); a=s.index('theorem '+name+'\n'); b=s.index(' := by',a)
 assert '\n```lean\n'+s[a:b]+'\n```' in report
result=dict(base=base,audited_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
 attempts=len(rows),modules=len(finals),theorem_audits=audit_count,protected_lean_modules=len(tracked),artifacts=artifacts,
 resource_policy=dict(env='J',lean_memory_mb=7000,MemoryHigh='5G',MemoryMax='7G',MemorySwapMax=0),
 report_signatures_match=True,generator_check=True)
(evidence/'history-fresh-final-audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='artifacts'},indent=2))
