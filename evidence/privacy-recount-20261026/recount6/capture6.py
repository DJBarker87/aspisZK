from pathlib import Path
import json,subprocess,hashlib,os
P=Path(__file__).resolve().parent; B=P.parent
pins=json.loads((P/'pins.json').read_text())['revisions']; rows=json.loads((B/'recount5/rows5.json').read_text()); manifest=[];cache={}
old={}
for d in ['recount4','recount5']:
 for x in json.loads((B/d/'manifest.json').read_text()):
  f=(B/d/x['snapshot']).resolve()
  if f.exists():old[x['blob']]=f

def read(k,path):
 key=(k,path)
 if key in cache:return cache[key]
 q=subprocess.run(['git','show',pins[k]+':'+path],capture_output=True)
 if q.returncode:cache[key]=None;return None
 raw=q.stdout;blob=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest(); f=old.get(blob,P/'objects'/(blob+'.txt'))
 if not f.exists():f.parent.mkdir(exist_ok=True);f.write_bytes(raw)
 manifest.append(dict(ref=k,revision=pins[k],path=path,blob=blob,sha256=hashlib.sha256(raw).hexdigest(),snapshot=os.path.relpath(f,P)))
 cache[key]=raw.decode();return cache[key]

def discover(k,patterns):
 q=subprocess.run(['git','grep','-l','-e','.',pins[k],'--',*patterns],capture_output=True,text=True)
 return [l.split(':',1)[1] for l in q.stdout.splitlines()]

audit=[]
for r in rows:
 path,_,decl=r.get('definition','').partition('#'); ss=[]
 # Every historical branch is checked where it was a defining witness, plus all active snapshots.
 ks=set(['research','rw','runjoin','reach','batch2','batch3']+[x['ref'] for x in r['definition_witnesses5']])
 for k in sorted(ks):
  s=read(k,path) if path else None
  if s is not None:ss.append({**next(x for x in reversed(manifest) if x['ref']==k and x['path']==path),'declaration':decl})
 audit.append(dict(id=r['id'],definition=r.get('definition'),sources=ss,changed_from5=[x['ref'] for x in ss if x['sha256'] not in {y['sha256'] for y in r['definition_witnesses5']}]))
 # Read all pinned prior supporting evidence again, not only definitions.
 for ev in r.get('recount5_evidence',[]):
  if ':' in ev:
   k,path=ev.split(':',1)
   if k in pins and path.startswith(('docs/','evidence/','design/')):read(k,path.split('#')[0])
for k in ['research','rw','runjoin','reach','batch2','batch3']:
 patterns=['docs/research/v8-r0-zk-20261009/lean/R1Z/PV_AL*.lean','evidence/pv-op254-20261027/lean/*.lean','evidence/pv-alib-20261027/*.md','evidence/pv-op254-20261027/*.md','evidence/pv-batch2*/**/*.md','evidence/pv-batch3*/**/*.md','evidence/pv-runjoin2*/*.md','evidence/pv-reach*/*.md']
 for path in discover(k,patterns):read(k,path)
for path in ['docs/research/v8-r0-zk-20261009/LOG.md','design/PRIVACY-LEDGER-20261026.md','evidence/pv-d188-20261027/AUDIT.md','evidence/pv-d188-20261027/rows.json','evidence/fidelity-check1-20261027/SDY_FINDING.md','tools/r1-cost-probe/rust-toolchain.toml']:
 for k in ['research','rw']:read(k,path)
for path in discover('rw',['evidence/pv-alib-20261027/376*.json','evidence/pv-alib-20261027/STRUCTURAL*.json','evidence/pv-alib-20261027/*GATE*.json','evidence/pv-op254-20261027/lean-receipts/3859*/*.json','evidence/pv-op254-20261027/FINAL-AUDIT.json','evidence/pv-op254-20261027/ROW-STATUS.json','evidence/pv-op254-20261027/accepted-receipts.json']):read('rw',path)
(P/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n');(P/'definition-audit6.json').write_text(json.dumps(audit,indent=2)+'\n')
print(len(audit),'rows',len(manifest),'objects; changed',[(x['id'],x['changed_from5']) for x in audit if x['changed_from5']])
