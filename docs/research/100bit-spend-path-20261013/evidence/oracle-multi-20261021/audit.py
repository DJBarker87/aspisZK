#!/usr/bin/env python3
"""Validate focused receipts and final source pins, without replaying Lean."""
import hashlib,json,pathlib,re,subprocess
root=pathlib.Path(__file__).resolve().parents[5]
base=root/'docs/research/100bit-spend-path-20261013'
ev=pathlib.Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
allowed={'propext','Classical.choice','Quot.sound'}
data=json.loads((ev/'manifest.json').read_text())
final=[]
for rec in data['attempts']:
 d=ev/(rec['module']+'-'+rec['attempt'])
 assert sha(d/'source.lean')==rec['source_sha256'],d
 assert json.loads((d/'receipt.json').read_text())==rec,d
 assert rec['exit'] is not None and rec['peak_rss_bytes'] is not None and rec['swaps'] is not None,d
 assert all(k in rec for k in ['argv','source_revision','deps_fingerprint','wall_seconds']),d
for src in sorted((base/'lean').glob('OracleDecisionMulti*.lean')):
 matches=[r for r in data['attempts'] if r['module']==src.stem and r['source_sha256']==sha(src) and r['exit']==0]
 assert matches,('no green final receipt',src)
 rec=matches[-1]
 for dep in rec['direct_imports']:
  assert dep['sha256'] and sha(pathlib.Path(dep['path']))==dep['sha256'],('changed dependency',src,dep)
 text=src.read_text()
 theorems=re.findall(r'^theorem\s+(\w+)',text,re.M)
 prints=re.findall(r'^#print axioms\s+(\w+)',text,re.M)
 assert sorted(theorems)==sorted(prints),(src,theorems,prints)
 assert len(rec['axioms'])==len(prints),(src,len(rec['axioms']),len(prints))
 for ax in rec['axioms']:
  if 'depends on axioms:' in ax:
   used=set(re.search(r'\[([^]]*)\]',ax).group(1).replace('\n','').replace(' ','').split(','))
   assert used<=allowed,(src,ax)
 assert not re.search(r'\b(sorry|admit|native_decide)\b|^axiom\s|set_option\s+(maxRecDepth|maxHeartbeats)',text,re.M),src
 final.append({k:rec[k] for k in ['module','attempt','source_sha256','source_revision','deps_fingerprint','exit','wall_seconds','peak_rss_bytes','swaps','axioms']})
changed=subprocess.check_output(['git','diff','--name-only','0f6232e31','--',str(base/'lean')],cwd=root,text=True).splitlines()
assert all(pathlib.Path(p).name.startswith('OracleDecisionMulti') for p in changed),changed
endpoints=[]
for name in ['R1FinalSoundnessBinPerQueryR19.lean','R1FinalSoundnessHeadline.lean']:
 p=base/'lean'/name
 if not p.exists():continue
 rel=str(p.relative_to(root))
 old=subprocess.check_output(['git','show','0f6232e31:'+rel],cwd=root)
 assert hashlib.sha256(old).hexdigest()==sha(p),name
 endpoints.append({'module':name,'base_sha256':hashlib.sha256(old).hexdigest(),'current_sha256':sha(p),'signature_diff':''})
(ev/'signature-audit.json').write_text(json.dumps({'base':'0f6232e31','claim':'No endpoint changed; no premise removal claimed.','endpoints':endpoints},indent=2)+'\n')
(ev/'audit.json').write_text(json.dumps({'schema':'oracle-multi-focused-audit-v1','revision_at_audit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),'attempt_count':len(data['attempts']),'final_module_count':len(final),'final_axiom_reports':sum(len(r['axioms']) for r in final),'final':final,'scope':'Focused cached-object checks; not a coherent frozen release replay.'},indent=2)+'\n')
print(json.dumps({'attempts':len(data['attempts']),'final_modules':len(final),'standard_axiom_reports':sum(len(r['axioms']) for r in final)}))
