from pathlib import Path
import subprocess,json,base64,lzma,hashlib
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-pool-leaves-20261105';H='dombarker@100.108.41.90'
ids=[json.loads(l)['attempt'] for l in(E/'NHC_ATTEMPTS.jsonl').read_text().splitlines()]
code='''from pathlib import Path
import json,hashlib,base64,subprocess,sys
b=Path(B);q=b/'NHC_SOURCE_COLLECTION-admission.json'
with(b/'NHC_SOURCE_COLLECTION-barrier.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(q)],stdout=f,stderr=subprocess.STDOUT)
a=json.loads(q.read_text())
if r.returncode or a.get('allowed') is not True:print(json.dumps(dict(admission=a,exit=r.returncode)));sys.exit(78)
blobs={};records=[]
for attempt in ids:
 rc=json.loads((b/attempt/'receipt.json').read_text())
 for name,expected in rc['source_hashes'].items():
  p=b/attempt/'sources'/name;raw=p.read_bytes();actual=hashlib.sha256(raw).hexdigest();assert actual==expected,(attempt,name)
  blobs.setdefault(actual,base64.b64encode(raw).decode());records.append(dict(attempt=attempt,relative=name,sha256=actual,bytes=len(raw)))
print(json.dumps(dict(records=records,blobs=blobs,admission=a,exit=r.returncode)))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input='B='+repr(B)+'\nids='+repr(ids)+'\n'+code,text=True,capture_output=True);(E/'NHC_SOURCE_COLLECTION.log').write_text(r.stderr);assert r.returncode==0,(r.returncode,r.stdout[:500],r.stderr[-1000:])
x=json.loads(r.stdout);D=E/'NHC_pinned_inputs';D.mkdir(exist_ok=True)
for h,v in x.pop('blobs').items():
 raw=base64.b64decode(v);assert hashlib.sha256(raw).hexdigest()==h
 p=D/(h+'.xz')
 if not p.exists():p.write_bytes(lzma.compress(raw,preset=6));(D/(h+'.sha256')).write_text(h+'\n')
for row in x['records']:
 p=E/row['attempt']/'sources'/row['relative'];p.parent.mkdir(parents=True,exist_ok=True)
 ref=dict(sha256=row['sha256'],bytes=row['bytes'],compressed=str((D/(row['sha256']+'.xz')).relative_to(E)),original_relative=row['relative'])
 p.with_name(p.name+'.REFERENCE.json').write_text(json.dumps(ref,indent=1)+'\n')
 if p.exists():assert hashlib.sha256(p.read_bytes()).hexdigest()==row['sha256'];p.unlink()
x['unique_inputs']=len(list(D.glob('*.xz')));(E/'NHC_SOURCE_COLLECTION.json').write_text(json.dumps(x,indent=1)+'\n');print(json.dumps(dict(sources=len(x['records']),unique_inputs=x['unique_inputs'])))
