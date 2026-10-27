from pathlib import Path
import json,hashlib,subprocess,os,re
P=Path(__file__).resolve().parent;pins=json.loads((P/'pins.json').read_text())['revisions'];manifest=json.loads((P/'manifest.json').read_text());ix={(x['ref'],x['path']):x for x in manifest}
def read(k,path,required=True):
 if (k,path) in ix:return (P/ix[k,path]['snapshot']).read_text()
 q=subprocess.run(['git','show',pins[k]+':'+path],capture_output=True)
 if q.returncode:
  if required:raise RuntimeError((k,path))
  return None
 raw=q.stdout;blob=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest();f=P/'objects'/(blob+'.txt');f.write_bytes(raw)
 x=dict(ref=k,revision=pins[k],path=path,blob=blob,sha256=hashlib.sha256(raw).hexdigest(),snapshot=os.path.relpath(f,P));ix[k,path]=x;manifest.append(x);return raw.decode()
# Fresh evidence, exact IDs: read-only reuse, not another compiler launch.
paths=['evidence/pv-batch1-20261027/powers-original-binding.json','evidence/pv-batch1-20261027/pole-original-binding.json','evidence/pv-op254-20261027/project-sources.json','evidence/pv-alib-20261027/resume3-project-preflight.json','evidence/pv-alib-20261027/resume3-candidate-cone.json','evidence/pv-cblib-20261027/52505.json','evidence/pv-cblib-20261027/52699.json','evidence/pv-cblib-20261027/resume9-join-slices-two-r01/collected-receipt.json','evidence/pv-cblib-20261027/resume9-reference-bodies.json']
for path in paths:read('rw',path)
for path in ['evidence/pv-runjoin20-20261027/receipt-37099.json','evidence/pv-runjoin20-20261027/out-37099.log','evidence/pv-runjoin20-20261027/STAGE1.md','evidence/pv-runjoin21-20261027/STAGE1-SELECTION.md']:
 read('runjoin',path)
for path in ['docs/research/v8-r0-zk-20261009/lean/R1Z/PV_B2_ErrorCounterexample.lean','docs/research/v8-r0-zk-20261009/lean/R1Z/PV_B2_C_ErrorRepair.lean','design/PV-BATCH2-20261027.md']:
 read('batch2',path)
project_map={x['module']:x for x in json.loads(read('rw','evidence/pv-op254-20261027/project-sources.json'))}
# Source closure for all six closing modules, separate from the consumer graph.
R='docs/research/v8-r0-zk-20261009/lean/';closure=[]
for root in ['R1Z.PV_AL_MoveClosure','R1Z.PV_AL_SplitSelected','R1Z.PV_AL_CircleSelected','PV_B1_Close254','PV_B1_Close230','PV_B1_Close258','R1Z.PV_CBL_CallbackPublication']:
 queue=[root];seen=set();unresolved=[];sources=[]
 for m in queue:
  if m in seen:continue
  seen.add(m)
  if not m.startswith(('R1Z.','R0Z.','PV_B1_','ProverRw')):continue
  candidates=([project_map[m]['path']] if m in project_map else [])+[R+m.replace('.','/')+'.lean']
  if m.startswith('R1Z.ProverRwFull'):candidates+=['docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/'+m.split('.')[-1]+'.lean']
  if m.startswith('PV_B1_'):candidates+=['evidence/pv-op254-20261027/lean/'+m+'.lean']
  s=None
  for path in candidates:
   s=read('rw',path,False)
   if s is not None:break
  if s is None:unresolved.append(m);continue
  
  if m in project_map:assert ix['rw',path]['sha256']==project_map[m]['sha256'],m
  sources.append({'module':m,**ix['rw',path]});queue.extend(re.findall(r'^import\s+(\S+)',s,re.M))
 closure.append(dict(root=root,sources=sources,unresolved=unresolved))
# Structural gate's pinned Rust files are independently hashed at candidate.
gate=json.loads(read('rw','evidence/pv-alib-20261027/STRUCTURAL-CIRCLE-GATE.json'));checks=[]
for name,x in gate['native_function_body_checks'].items():
 raw=read('rw',x['path']).encode();h=hashlib.sha256(raw).hexdigest();checks.append(dict(function=name,path=x['path'],expected=x['file_sha256'],actual=h,match=h==x['file_sha256']))
 assert h==x['file_sha256'],name
v=json.loads(read('rw','evidence/pv-batch1-20261027/powers-original-binding.json'));s=read('rw',v['rust_path']);checks.append(dict(function='powers original weights source',path=v['rust_path'],expected=v['rust_sha256'],actual=hashlib.sha256(s.encode()).hexdigest(),match=hashlib.sha256(s.encode()).hexdigest()==v['rust_sha256']))
assert checks[-1]['match']
# Closing modules remain byte-identical to the exact source revision recorded in final audits.
freeze_checks=[]
for c in closure[:6]:
 rev='e9c42631f30c64653595ab2999de42714de69953' if c['root'].startswith('R1Z.PV_AL_') else 'ac65f872a23a08bf498f710f63e0c0a5187e2189'
 for x in c['sources']:
  # New AL/B1 source cone only; upstream imported source cohorts retain their own authorities.
  if '/PV_AL_' not in x['path'] and not x['path'].startswith(('evidence/pv-op254-20261027/lean/','evidence/pv-batch1-20261027/lean/')):continue
  q=subprocess.run(['git','show',rev+':'+x['path']],capture_output=True)
  same=q.returncode==0 and hashlib.sha256(q.stdout).hexdigest()==x['sha256'];freeze_checks.append(dict(module=x['module'],path=x['path'],audit_revision=rev,current_sha256=x['sha256'],matches=same));assert same,x['module']
(P/'closing-source-cones6.json').write_text(json.dumps(closure,indent=2)+'\n');(P/'native-pin-checks6.json').write_text(json.dumps(checks,indent=2)+'\n');(P/'closing-freeze-checks6.json').write_text(json.dumps(freeze_checks,indent=2)+'\n');(P/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print('Source cones',[(c['root'],len(c['sources']),c['unresolved']) for c in closure]);print('Native pin checks',len(checks),'freeze checks',len(freeze_checks))
