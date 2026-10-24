from pathlib import Path
import hashlib,json,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/port13gate-20261024';L=R/'docs/research/100bit-spend-path-20261013/lean'
objects={}
for receipt in E.glob('lean-*/receipt.json'):
 x=json.loads(receipt.read_text())
 for name,obj in x['deps_fingerprint']['selected_objects'].items():
  if name.endswith('.olean'):
   source=L/(name[:-6]+'.lean')
   if source.exists():objects[obj['path']]={'local_source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'object_sha256':obj['sha256']}
code='''from pathlib import Path
import hashlib,json
objects=REPLACE
out=[]
for name,expected in objects.items():
 p=Path(name);s=p.with_suffix('.lean')
 object_hash=hashlib.sha256(p.read_bytes()).hexdigest()
 row={'object':name,**expected,'current_object_sha256':object_hash}
 row['host_source_sha256']=hashlib.sha256(s.read_bytes()).hexdigest() if s.exists() else None
 row['source_assessment']='matching adjacent source' if row['host_source_sha256']==expected['local_source_sha256'] else 'adjacent source unavailable; inherited object evidence only'
 assert object_hash==expected['object_sha256'],row
 assert row['host_source_sha256'] is None or row['host_source_sha256']==expected['local_source_sha256'],row
 out.append(row)
print(json.dumps(out,indent=2))
'''.replace('REPLACE',repr(objects))
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True,capture_output=True)
(E/'cache-source-assessment.json').write_text(r.stdout)
(E/'cache-source-assessment-command.json').write_text(json.dumps({'command':['ssh','dombarker@100.108.41.90','python3','-'],'stdin_sha256':hashlib.sha256(code.encode()).hexdigest(),'exit_status':r.returncode,'stderr':r.stderr},indent=2)+'\n')
assert r.returncode==0,r.stderr
rows=json.loads(r.stdout)
prior=R/'docs/research/100bit-spend-path-20261013/evidence/multiproof-cone-20261021/MultiproofConeP6Frozen2Stage-4/receipt.json'
history=json.loads(prior.read_text())
for row in rows:
 if row['host_source_sha256'] is None:
  assert row['object'].endswith('/MultiproofConeP6Frozen2Stage.olean')
  assert history['exit']==0 and history['source_sha256']==row['local_source_sha256']
  assert history['object_sha256']==row['object_sha256']
  row.update({'source_assessment':'exact historical source and object match; no new identity gate',
    'historical_receipt':str(prior.relative_to(R)),
    'historical_receipt_sha256':hashlib.sha256(prior.read_bytes()).hexdigest(),
    'historical_revision':history['source_revision']})
(E/'cache-source-assessment.json').write_text(json.dumps(rows,indent=2)+'\n')
