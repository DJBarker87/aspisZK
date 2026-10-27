"""Read-only native boundary availability; separate authorized own receipts from copied caches."""
import pathlib,json,subprocess,shlex,hashlib
R=pathlib.Path(__file__).resolve().parents[2];E=R/'evidence/pv-reach-20261027/resume9';H='/home/dombarker/project-offloads/codex-pv-reach-20261027'
rows=json.load(open(E/'native-project-closure.json'));old={r['module'] for r in json.load(open(E/'project-closure.json'))};extra=[r for r in rows if r['module'] not in old]
receipts={}
for p in E.parent.rglob('receipt-*.json'):
 try:r=json.loads(p.read_text())
 except (ValueError,OSError):continue
 if r.get('accepted') and r.get('target'):receipts.setdefault(r['target'].replace('/','.'),[]).append(r)
script='''import pathlib,json,hashlib,sys
rows=json.load(sys.stdin);h=pathlib.Path('/home/dombarker/project-offloads/codex-pv-reach-20261027/lean');shared=pathlib.Path('/home/dombarker/project-offloads/aspis-joint-20261019');out=[]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest() if p.is_file() else None
for r in rows:
 rel=r['module'].replace('.','/');p=h/'objects'/(rel+'.olean');s=shared/'sources'/(rel+'.lean')
 out.append(dict(module=r['module'],authority=r['authority'],expected_source_sha256=r['sha256'],private_object_exists=p.is_file(),private_object_path=str(p),private_object_sha256=sha(p),resolved_object_path=str(p.resolve()),shared_source_sha256=sha(s),shared_object_sha256=sha(shared/'objects'/(rel+'.olean'))))
print(json.dumps(out,indent=2))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(script)],input=json.dumps(extra),capture_output=True,text=True,check=True)
checks=json.loads(r.stdout)
for row in checks:
 own=[r for r in receipts.get(row['module'],[]) if r.get('source_sha256')==row['expected_source_sha256']]
 row['matching_own_prior_build_receipts']=[r['attempt'] for r in own]
 row['source_authorized_existing_object']=row['private_object_exists'] and (bool(own) or (row['authority']=='EJR' and row['shared_source_sha256']==row['expected_source_sha256'] and row['private_object_sha256']==row['shared_object_sha256']))
(E/'native-availability.json').write_text(json.dumps(checks,indent=2)+'\n')
print('extra modules',len(checks),'authorized cached',sum(r['source_authorized_existing_object'] for r in checks),'private builds needed',sum(not r['source_authorized_existing_object'] for r in checks))
