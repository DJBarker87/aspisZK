"""Collect exact per-target receipts and refuse promotion of stale/failed objects."""
from pathlib import Path
import json,hashlib,re,subprocess,shlex
E=Path('evidence/pv-batch2-20261027/batch2e');L=Path('docs/research/v8-r0-zk-20261009/lean');h5=json.loads((E/'H5-SOURCE-PINS.json').read_text());receipts=[];accepted={}
for p in sorted(E.glob('398[0-9][0-9].json')):
 j=json.loads(p.read_text());receipts.append(j)
 if j.get('exit_status')==0 and j.get('accepted_axioms'):
  m=j['module'];path=Path(h5[m]['path']) if m in h5 else L/(m+'.lean')
  if hashlib.sha256(path.read_bytes()).hexdigest()==j['source_sha256']:
   accepted[m]=dict(module=m,path=str(path),attempt=j['attempt'],source_sha256=j['source_sha256'],source_revision=j['source_revision'],axioms=j['parsed_axioms'])
(E/'LEAN-RECEIPTS.json').write_text(json.dumps(receipts,indent=2)+'\n')
(E/'ACCEPTED-PROGRESS.json').write_text(json.dumps(dict(scope='exact successful current sources; row credit requires structural/native/combined audit evidence separately',sources=list(accepted.values())),indent=2)+'\n')
admissions=[]
for p in sorted((E/'admission-probes').glob('*.json')):
 j=json.loads(p.read_text());r=j.get('reservation') or {};log=j.get('log','');tail={}
 try:tail=json.loads(log.splitlines()[-1])
 except (ValueError,IndexError):pass
 admissions.append(dict(path=str(p),exit=j.get('exit'),allowed=r.get('allowed'),utc=r.get('utc'),compiler_launched=False,bounded_reserved_bytes=tail.get('bounded_reserved_bytes'),projected_reserved_bytes=tail.get('projected_reserved_bytes')))
(E/'ADMISSION-SUMMARY.json').write_text(json.dumps(admissions,indent=2)+'\n')
code='''from pathlib import Path
import sys,json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-batch2-20261027');r=[]
for a in json.load(sys.stdin):
 p=D/'lean-objects'/(a['module']+'.olean');a['object_path']=str(p);a['object_sha256']=hashlib.sha256(p.read_bytes()).hexdigest();a['object_bytes']=p.stat().st_size;r.append(a)
print(json.dumps(r))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(list(accepted.values())),capture_output=True,text=True,check=True);(E/'OUTPUT-OBJECT-PINS.json').write_text(json.dumps(json.loads(r.stdout),indent=2)+'\n')
print(len(receipts),'charged',len(accepted),'accepted current sources; refusals separately retained')
