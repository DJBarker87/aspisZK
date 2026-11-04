from pathlib import Path
import json,lzma,subprocess,base64
E=Path(__file__).resolve().parent
payload=base64.b64encode(Path('evidence/coherent-20261102/NER_STREAM_B_COHORT.jsonl.xz').read_bytes()).decode()
code='''from pathlib import Path
import json,lzma,base64,hashlib,shutil
P=Path('/home/dombarker/project-offloads'); C=P/'codex-cx-slice-q-mul6-cache-20261029/NER_cohort';C.mkdir(exist_ok=True)
rows=[json.loads(l) for l in lzma.decompress(base64.b64decode(PAYLOAD)).decode().splitlines()];out=[]
for r in rows:
 p=Path(r['object_path']);q=C/(r['module'].replace('.','/')+'.olean');q.parent.mkdir(parents=True,exist_ok=True)
 assert hashlib.sha256(p.read_bytes()).hexdigest()==r['object_sha256'],str(p)
 if not q.exists():shutil.copyfile(p,q)
 assert hashlib.sha256(q.read_bytes()).hexdigest()==r['object_sha256'],str(q)
 item=dict(module=r['module'],source=str(p),destination=str(q),sha256=r['object_sha256'],companions=[])
 for z in r['companions']:
  # manifest companion records retain explicit paths/hashes
  zp=Path(z['path']);zq=C/zp.relative_to(p.parent) if zp.parent==p.parent else None
  if zq is None:raise RuntimeError(z)
  zq=q.parent/zp.name
  if not zq.exists():shutil.copyfile(zp,zq)
  assert hashlib.sha256(zq.read_bytes()).hexdigest()==z['sha256']
  item['companions'].append(dict(source=str(zp),destination=str(zq),sha256=z['sha256']))
 if r['module'] in ['RPt_FIo_ScalarBridge','RPt_FIo_ReduceFacts','RPt_FIo_ReduceBounds','RPt_JFr_TX2_DotBounds']:
  s=Path(r['source_path']).read_bytes();assert hashlib.sha256(s).hexdigest()==r['source_sha256'];item['source_text']=s.decode()
 out.append(item)
print(json.dumps(out))
'''.replace('PAYLOAD',repr(payload))
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,capture_output=True,text=True)
(E/'NFE_COHORT_TRANSPORT.json').write_text(json.dumps(dict(exit=r.returncode,stderr=r.stderr)))
assert r.returncode==0,r.stderr
out=json.loads(r.stdout);raw=json.dumps(out).encode();(E/'NFE_COHORT_IMPORTS.json.xz').write_bytes(lzma.compress(raw));import hashlib
(E/'NFE_COHORT_IMPORTS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
print('pinned',len(out),'cohort objects')
