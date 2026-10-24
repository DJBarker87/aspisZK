#!/usr/bin/env python3
"""Read-only receipt/scope validation, with a derived small manifest."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/port8effects-20261024';L=R/'docs/research/100bit-spend-path-20261013/lean'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();allowed={'propext','Classical.choice','Quot.sound'}
limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
rows=[];green=[]
for p in sorted(E.glob('lean-*/receipt.json')):
 x=json.loads(p.read_text());assert x['limits']==limits,(p,x['limits'])
 assert x['swaps']=='0',p
 for f,h in x['source_hashes'].items():assert sha(p.parent/'sources'/f)==h,(p,f)
 for line in x['print_axioms']:
  m=re.search(r'axioms: \[([^\]]*)\]',line)
  if x['exit_status']==0 and m:assert {a.strip() for a in m[1].split(',')}<=allowed,(p,line)
 admission=json.loads((E/(x['attempt']+'-reservation.json')).read_text())
 assert admission['reserved_bytes']+admission['additional_bytes']<=55*1024**3,p
 if x['exit_status']==0:green.append(x)
 rows.append({k:x[k] for k in ['attempt','sources','source_revision','exit_status','wall_seconds','peak_rss_kib','swaps','source_hashes','print_axioms']})
assert len(rows)<=100
assessment=json.loads((E/'object-source-assessment.json').read_text())
coverage={}
for p in sorted(L.glob('Port8EFF_*.lean')):
 clean=re.sub(r'/\-.*?\-/|--[^\n]*','',p.read_text(),flags=re.S)
 assert not re.search(r'\b(sorry|axiom|admit|native_decide)\b|set_option\s+(maxHeartbeats|maxRecDepth)',clean),p
 matches=[x for x in green if x['source_hashes'].get(p.name)==sha(p)];assert matches,p
 final=matches[-1]
 own=assessment['own_objects'][p.stem+'.olean']
 for obj in final['deps_fingerprint']['selected_objects'].values():
  q=Path(obj['path'])
  if q.parent.name=='codex-cx-port8effects-20261024' and q.suffix=='.olean':
   assert assessment['own_objects'][q.name]['sha256']==obj['sha256'],(p,q)
 for name,h in final['deps_fingerprint']['direct_source_hashes'].items():
  local=L/(name.replace('.','/')+'.lean')
  if name.startswith('Port8EFF_'):assert sha(local)==h,(p,name)
 coverage[p.name]={'sha256':sha(p),'attempt':final['attempt'],'object':own}
for v in assessment['selected_dependencies'].values():
 if 'host_source_matches_local' in v:assert v['host_source_matches_local'],v
pins=json.loads((E/'source-inventory.json').read_text())
assert len(pins['operations'])==13
for path,pin in pins['pins'].items():assert sha(R/path)==pin['sha256'],path
base='a23a58fb09da964d305f761d0ecdfc083eecce55'
changed=subprocess.check_output(['git','diff','--name-only',base],cwd=R,text=True).splitlines()
for path in changed:
 assert path.startswith(('evidence/port8effects-20261024/','tools/port8effects-20261024/','docs/research/100bit-spend-path-20261013/lean/Port8EFF_')),path
for directory in [E,R/'tools/port8effects-20261024']:
 for p in directory.rglob('*'):
  if not p.is_file():continue
  assert p.suffix not in {'.olean','.ir','.tar','.gz','.elf'},p
  assert p.stat().st_size<=5_000_000,p
for name in ['reader','control','skeleton']:
 subprocess.run(['python3',str(R/f'tools/port8effects-20261024/Port8EFF_{name}_gen.py'),'--check'],check=True)
subprocess.run(['python3',str(R/'tools/port8effects-20261024/Port8EFF_source_audit.py')],check=True)
audit=[x for x in green if x['sources']==['Port8EFF_Audit.lean']][-1]
out={'schema':'focused-extractor-proof-packet-v1','status':'Partial: checkpoint8/current18 installed; complete current reader effects, first-source accepted-driver checkpoint segment and actual second powers operand established. Batch/prepare sampler embedding and both security targets remain open.',
 'lean_attempts':len(rows),'kani_runs':0,'final_audit':audit['attempt'],'source_revision_at_audit':audit['source_revision'],'final_audit_metrics':{k:audit[k] for k in ['exit_status','wall_seconds','peak_rss_kib','swaps']},'final_sources':coverage,'attempts':rows,
 'qualification':'Focused cached dependency reuse with current host-source assessment; not a coherent release rebuild or a new ELF identity gate. Failed declaration axiom outputs are rejected evidence. No full frozen manifest.',
 'unchanged_elf_pins':{'default':'f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4','devnet':'63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299','pool':'121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548'}}
(E/'manifest.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:out[k] for k in ['lean_attempts','kani_runs','final_audit','final_audit_metrics']},indent=2))
