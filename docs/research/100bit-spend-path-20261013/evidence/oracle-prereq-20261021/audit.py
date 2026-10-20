#!/usr/bin/env python3
"""Audit current focused source/evidence without rerunning unchanged Lean."""
import hashlib,json,pathlib,re,subprocess
here=pathlib.Path(__file__).resolve().parent
root=here.parents[4]
base=root/'docs/research/100bit-spend-path-20261013'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((here/'manifest.json').read_text())
checks=[]
for r in manifest['attempts']:
 packet=here/f"{r['module']}-{r['attempt']}"
 assert sha(packet/'source.lean')==r['source_sha256'],f'snapshot mismatch {packet}'
 assert json.loads((packet/'receipt.json').read_text())==r,f'receipt mismatch {packet}'
 assert all(r[k] is not None for k in ['source_revision','deps_fingerprint','exit','wall_seconds','peak_rss_bytes','swaps'])

for src in sorted((base/'lean').glob('OracleDecisionPrereq*.lean')):
 attempts=[r for r in manifest['attempts'] if r['module']==src.stem and r['exit']==0 and r['source_sha256']==sha(src)]
 assert attempts, f'no green current source: {src}'
 r=attempts[-1]
 audits=r['axioms']
 declared=re.findall(r'^(?:private )?theorem\s+(\w+)',src.read_text(),re.M)
 printed=re.findall(r'^#print axioms (\w+)',src.read_text(),re.M)
 assert set(declared)==set(printed),(src,declared,printed)
 assert len(audits)==len(declared),(src,len(audits),len(declared))
 for line in audits:
  deps=re.search(r'\[([^\]]*)\]',line)
  if deps:
   assert set(x.strip() for x in deps[1].split(',') if x.strip()) <= {'propext','Classical.choice','Quot.sound'},line
 for dep in r['direct_imports']:
  assert sha(pathlib.Path(dep['path']))==dep['sha256'],f'changed direct import {dep}'
 assert sha(here/f"{src.stem}-{r['attempt']}"/'source.lean')==sha(src)
 assert not re.search(r'\b(sorry|axiom|admit|native_decide|maxRecDepth|maxHeartbeats)\b',re.sub(r'/-.*?-/', '',src.read_text(),flags=re.S)),src
 checks.append({'module':src.stem,'attempt':r['attempt'],'source_sha256':sha(src),'theorems':len(declared),
  'wall_seconds':r['wall_seconds'],'peak_rss_bytes':r['peak_rss_bytes'],'swaps':r['swaps']})
changed=subprocess.check_output(['git','diff','--name-status','26fc9ca35','--',str(base/'lean')],cwd=root,text=True)
for line in changed.splitlines():
 status,path=line.split('\t',1)
 assert status=='A' and pathlib.Path(path).name.startswith('OracleDecisionPrereq'),line
result={'schema':'oracle-decision-prereq-audit-v1','base':'26fc9ca35','source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),
 'modules':checks,'theorems':sum(c['theorems'] for c in checks),'attempt_count':len(manifest['attempts']),
 'failed_attempts':[{'module':r['module'],'attempt':r['attempt'],'exit':r['exit']} for r in manifest['attempts'] if r['exit']!=0],
 'existing_lean_changes':False,'endpoint_signature_diff':'empty','scope':'Focused cache-based checks; not a new coherent frozen release replay.'}
(here/'audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
