"""Read-only complete source/object/dependency close check after final audits."""
from pathlib import Path
import json,subprocess,hashlib,re,shlex,datetime
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-l2c-20261028/resume-d371';L=R/'evidence/pv-l2c-20261028/resume-d369'
resolution=json.loads((L/'focused-resolution.json').read_text());assert not resolution['unpinned']
res=resolution['resolved'];cache=json.loads((L/'cache-plan.json').read_text())['objects']
accepted={}
for p in sorted(L.glob('receipt-*.json')):
 x=json.loads(p.read_text())
 if x.get('accepted'):accepted[(x['module'],x['source_sha256'])]=x
expected={};unresolved=[]
for m,x in res.items():
 if 'imports' not in x:expected[m]=dict(sha256=x['object_sha256'],kind='external');continue
 if (m,x['sha256']) in accepted:
  a=accepted[(m,x['sha256'])];expected[m]=dict(sha256=None,kind='own accepted compiler receipt',source_sha256=x['sha256'],attempt=a['attempt'],dependencies=a['dependencies'])
 elif m in cache and cache[m].get('source',{}).get('sha256')==x['sha256']:
  expected[m]=dict(sha256=cache[m]['sha256'],kind='previous complete pinned cache check',source_sha256=x['sha256'])
 else:unresolved.append(m)
assert not unresolved,unresolved
code=r'''import json,pathlib,hashlib,sys
z=json.load(sys.stdin);expected=z['expected'];res=z['resolution'];H=pathlib.Path('/home/dombarker/project-offloads/codex-pv-l2c-20261028/lean');env=json.load(open(H/'J.json'));roots=[H/'objects']+[pathlib.Path(x) for x in env['LEAN_PATH'].split(':')];objects={};fail=[]
for m,x in expected.items():
 rel=m.replace('.','/')+'.olean';p=next((root/rel for root in roots if (root/rel).is_file()),None)
 if p is None:fail.append([m,'missing actual object']);continue
 h=hashlib.sha256(p.read_bytes()).hexdigest()
 if x['sha256'] is not None and h!=x['sha256']:fail.append([m,'object mismatch',h,x['sha256']])
 if x['kind']=='own accepted compiler receipt':
  s=H/'sources'/(m.replace('.','/')+'.lean');sh=hashlib.sha256(s.read_bytes()).hexdigest()
  if sh!=x['source_sha256']:fail.append([m,'compiled-source mismatch',sh,x['source_sha256']])
 objects[m]=dict(path=str(p),sha256=h,source_sha256=x.get('source_sha256'),authority=x['kind'],attempt=x.get('attempt'))
for m,x in expected.items():
 for d,v in x.get('dependencies',{}).items():
  if d not in objects or objects[d]['sha256']!=v['sha256']:fail.append([m,'direct dependency changed',d,v,objects.get(d)])
 for d in res[m].get('imports',[]):
  if d not in objects:fail.append([m,'closure missing import',d])
print(json.dumps(dict(objects=objects,failures=fail,env_sha256=hashlib.sha256((H/'J.json').read_bytes()).hexdigest(),all_direct_and_transitive_imports_present=not fail)))
'''
p=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(dict(expected=expected,resolution=res)),text=True,capture_output=True)
(E/'final-closure-transport.log').write_text(p.stderr);assert p.returncode==0,p.stderr
out=json.loads(p.stdout);assert not out['failures'],out['failures']
out.update(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),resolution_head=resolution['head'],resolution_sha256=hashlib.sha256((L/'focused-resolution.json').read_bytes()).hexdigest())
(E/'final-closure-check.json').write_text(json.dumps(out,indent=2)+'\n')
assert len([p for p in L.glob('receipt-*.json')])==100
for a in [50397,50398,50399]:
 x=json.loads((L/f'receipt-{a}.json').read_text());assert x['accepted'] and x['exit']==0
 ax=set(re.findall(r'(?<![A-Za-z0-9_.])(?:propext|Classical.choice|Quot.sound|sorryAx)(?![A-Za-z0-9_.])',' '.join(x['axioms'])))
 assert 'sorryAx' not in ax
outsummary=dict(projects=sum('imports' in x for x in res.values()),externals=sum('imports' not in x for x in res.values()),objects=len(out['objects']),all_source_authorities_resolved=True,all_actual_prefix_objects_checked=True,all_accepted_direct_dependencies_unchanged=True,final_audits=[50397,50398,50399],axioms=['propext','Classical.choice','Quot.sound'])
(E/'CLOSE-SUMMARY.json').write_text(json.dumps(outsummary,indent=2)+'\n');print(json.dumps(outsummary))
