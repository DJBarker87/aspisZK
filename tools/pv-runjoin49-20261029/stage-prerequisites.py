from pathlib import Path
import json,hashlib,subprocess,shlex,lzma
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin49-20261029';x=json.loads((E/'encoder49-resolution.json').read_text());src=json.loads((E/'encoder49-project-sources.json').read_text());plan=json.loads((E/'build-plan.json').read_text());assert not x['unpinned']
needed=set()
def need(m):
 if m in needed or m in plan['modules'] or m not in src:return
 needed.add(m)
 for d in x['resolved'][m]['imports']:need(d)
for root in __import__('sys').argv[1:]:need(root)
new={m:v for m,v in x['resolved'].items() if m in needed};seen=set();order=[]
def visit(m):
 if m in seen or m not in new:return
 seen.add(m)
 for d in new[m]['imports']:visit(d)
 order.append(m)
for m in new:visit(m)
assert 1<=len(order)<=300
for m,v in x['resolved'].items():
 if m in plan['modules']:assert v['sha256']==plan['modules'][m]['sha256'],m
for m,v in new.items():
 assert v['authority']
 assert hashlib.sha256(src[m].encode()).hexdigest()==v['sha256']
 v['revision']=x['head'];plan['modules'][m]=v
payload=dict(workspace=plan['workspace'],sources={m:src[m] for m in order},plan=plan)
code='''import json,sys,pathlib,hashlib
x=json.load(sys.stdin);p=pathlib.Path(x['workspace'])
for m,s in x['sources'].items():
 q=p/'sources'/(m.replace('.','/')+'.lean');o=p/'objects'/(m.replace('.','/')+'.olean');assert not o.exists();assert not q.exists()
 q.parent.mkdir(parents=True,exist_ok=True);q.write_text(s);assert hashlib.sha256(q.read_bytes()).hexdigest()==x['plan']['modules'][m]['sha256']
(p/'build-plan.json').write_text(json.dumps(x['plan']));print('staged',len(x['sources']))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(payload),text=True,capture_output=True);assert r.returncode==0,r.stderr
(E/'encoder49-staging.json').write_text(json.dumps(dict(exit=r.returncode,stdout=r.stdout,stderr=r.stderr,order=order,pins=new),indent=2)+'\n');(E/'build-plan.json').write_text(json.dumps(plan,indent=2)+'\n');b=(E/'encoder49-project-sources.json').read_bytes();(E/'encoder49-project-sources.json.xz').write_bytes(lzma.compress(b));(E/'encoder49-project-sources.json.sha256').write_text(hashlib.sha256(b).hexdigest()+'  encoder49-project-sources.json\n');print(' '.join(order))
