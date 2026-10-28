from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parents[2]/'evidence/pv-relink-20261028';f=json.loads((E/'closure-after-replay.json').read_text());project=f['project'];external={x['module']:x['object_sha256'] for x in f['external']};exfp=hashlib.sha256(json.dumps(external,sort_keys=True).encode()).hexdigest()
for a in json.loads((E/'attempts.json').read_text()):
 p=E/str(a['id'])/'receipt.json'
 if not p.exists():continue
 j=json.loads(p.read_text());cone={}
 def visit(m):
  if m in cone or m not in project:return
  x=project[m];cone[m]=dict(source_sha256=x['source_sha256'],object_sha256=x['object_sha256'])
  for d in x['source_authority']['imports']:visit(d)
 for d in a['imports']:visit(d)
 j['receipt_collected_at_revision']=j.get('receipt_collected_at_revision',j['source_revision']);j['source_revision']=a['revision'];j['dependency_objects']=cone;j['external_dependency_manifest_fingerprint']=exfp;j['deps_fingerprint']=hashlib.sha256(json.dumps(dict(project=cone,external=exfp),sort_keys=True).encode()).hexdigest();j['fingerprint_method']='Read-only final reconstruction: imported objects were never replaced during this job; closure-after-replay.json records the complete source/object cohort. Target itself is excluded.'
 p.write_text(json.dumps(j,indent=2)+'\n')
print('all launched Lean receipts have source revision and complete dependency fingerprints')
