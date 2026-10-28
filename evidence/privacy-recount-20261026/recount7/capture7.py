from pathlib import Path
import json,subprocess,hashlib,os
P=Path(__file__).resolve().parent; B=P.parent
pins=json.loads((P/'pins.json').read_text())['revisions'];rows=json.loads((B/'recount6/rows6.json').read_text());manifest=[];cache={};old={}
for d in ['recount4','recount5','recount6']:
 for x in json.loads((B/d/'manifest.json').read_text()):
  f=(B/d/x['snapshot']).resolve()
  if f.exists():old[x['blob']]=f

def read(k,path):
 if (k,path) in cache:return cache[k,path]
 q=subprocess.run(['git','show',pins[k]+':'+path],capture_output=True)
 if q.returncode:cache[k,path]=None;return None
 raw=q.stdout;blob=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest();f=old.get(blob,P/'objects'/(blob+'.txt'))
 if not f.exists():f.parent.mkdir(exist_ok=True);f.write_bytes(raw)
 manifest.append(dict(ref=k,revision=pins[k],path=path,blob=blob,sha256=hashlib.sha256(raw).hexdigest(),snapshot=os.path.relpath(f,P)));cache[k,path]=raw.decode();return cache[k,path]
def discover(k,patterns):
 q=subprocess.run(['git','grep','-l','-e','.',pins[k],'--',*patterns],capture_output=True,text=True)
 return [l.split(':',1)[1] for l in q.stdout.splitlines()]
audit=[]
active=['research','rw','runjoin','reach','l2c','dlib','b3p6','kstub','gate6']
for r in rows:
 path,_,decl=r.get('definition','').partition('#');ss=[];missing=[]
 for k in sorted(set(active+[x['ref'] for x in r['definition_witnesses6']])):
  s=read(k,path) if path else None
  if s is not None:ss.append({**next(x for x in reversed(manifest) if x['ref']==k and x['path']==path),'declaration':decl})
  else:missing.append(k)
 audit.append(dict(id=r['id'],definition=r.get('definition'),sources=ss,missing=missing,changed_from6=[x['ref'] for x in ss if x['sha256'] not in {y['sha256'] for y in r['definition_witnesses6']}]))
 for ev in r.get('recount6_evidence',[]):
  if ':' in ev:
   k,path=ev.split(':',1)
   if k in pins and path.startswith(('docs/','evidence/','design/','tools/')):read(k,path.split('#')[0])
patterns={
 'rw':['evidence/pv-batch3*/*.md','evidence/pv-batch2*/*.md','evidence/pv-relink*/*.md','evidence/pv-relink*/*.json','evidence/pv-batch3*/**/receipt.json','evidence/pv-batch2*/**/receipt.json','docs/research/v8-r0-zk-20261009/lean/R1Z/PV_B3*.lean','docs/research/v8-r0-zk-20261009/lean/R1Z/PV_B2*.lean','docs/research/v8-r0-zk-20261009/lean/R1Z/PV_Relink*.lean'],
 'research':['evidence/pv-kscan*/*.md','evidence/pv-kscan*/rows*.json','evidence/kani-mitig*/KMX_FINDING.md','evidence/kani-reverify*/KM*_FINDING.md','evidence/kani-diag*/KDX_FINDING.md'],
 'runjoin':['evidence/pv-runjoin2*/*.md','evidence/pv-runjoin3*/*.md','docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_*2[3-9].lean','docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_*3*.lean'],
 'dlib':['evidence/pv-dlib*/*.md','design/PV-DLIB*.md'],
 'b3p6':['evidence/pv-b3p6*/*.md','design/PV-B3P6*.md'],
 'kstub':['evidence/pv-kstub*/*.md'],
 'gate6':['evidence/pv-gate6*/*.md','evidence/pv-integ4*/*.md','evidence/pv-integ4*/*comparison.json','evidence/pv-gate6*/*status*.json'],
 'reach':['evidence/pv-reach*/*REPORT*.md','evidence/pv-reach*/*STATUS*.md'],
 'l2c':['evidence/pv-l2c*/*.md']}
for k,ps in patterns.items():
 for path in discover(k,ps):read(k,path)
for k in ['research','rw']:
 for path in ['docs/research/v8-r0-zk-20261009/LOG.md','design/PRIVACY-LEDGER-20261026.md']:read(k,path)
(P/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n');(P/'definition-audit7.json').write_text(json.dumps(audit,indent=2)+'\n')
print('rows',len(audit),'manifest',len(manifest),'changed',[(x['id'],x['changed_from6']) for x in audit if x['changed_from6']])
