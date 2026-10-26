"""Read-only coherent-name and committed source-pin lookup, not a compiler launcher."""
from pathlib import Path
import json,subprocess,hashlib
E=Path(__file__).resolve().parent;R=E.parents[1]
p=json.loads((E/'RPz4_source-plan.json').read_text());names=p['unresolved']
code='''import json,hashlib
from pathlib import Path
b=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025');cfg=json.loads((b/'Rc7_002.json').read_text());roots=[b/'.lake/build/lib/lean']+list(map(Path,cfg['env']['LEAN_PATH'].split(':')))
out={}
for n in NAMES:
 found=[]
 for root in dict.fromkeys(roots):
  f=root/(n.replace('.','/')+'.olean')
  if f.is_file():found.append({'path':str(f),'sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'bytes':f.stat().st_size})
 out[n]=found
print(json.dumps(out))
'''.replace('NAMES',repr(names))
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
objects=json.loads(r.stdout);hashes={n:v[0]['sha256'] for n,v in objects.items() if v};records=[]
r=subprocess.run(['rg','-l','|'.join(hashes.values()),'docs','evidence','-g','*.json','-g','!RPz4*'],cwd=R,capture_output=True,text=True)
for f in r.stdout.splitlines():
 try:z=json.loads((R/f).read_text())
 except:continue
 def walk(v,path=''):
  if isinstance(v,dict):
   direct=' '.join(str(t) for t in v.values() if isinstance(t,str))
   for n,h in hashes.items():
    if h in direct and len(str(v))<6000:records.append({'module':n,'file':f,'key':path,'record':v})
   for k,w in v.items():
    if isinstance(w,(dict,list)):walk(w,path+'/'+k)
  elif isinstance(v,list):
   for i,w in enumerate(v):walk(w,path+'/'+str(i))
 walk(z)
a=json.loads((E/'RPz4_aliases.json').read_text());out={}
g=json.loads((R/'evidence/replay-dry-20261026/RPy_graph.json').read_text())['modules']
for n in names:
 candidates=p['modules'][n]['candidates'];hs={hashlib.sha256((R/f).read_bytes()).hexdigest():f for f in candidates};hits={}
 for v in records:
  h=v['record'].get('source_sha256')
  if v['module']==n and h in hs:hits[h]={'path':hs[h],'sha256':h,'pin':v['file']}
 if len(hits)>1:
  expected=set(g.get(n,{}).get('imports',[]))
  hits={h:v for h,v in hits.items() if set(['Init']+[line[7:].strip() for line in (R/v['path']).read_text().splitlines() if line.startswith('import ')])==expected}
 out[n]={'objects_in_order':objects.get(n,[]),'source_matches':list(hits.values())}
 if len(hits)==1:
  v=next(iter(hits.values()));a[n]={'path':v['path'],'sha256':v['sha256'],'reason':'source/object hash pairing for selected coherent object: '+v['pin']}
(E/'RPz4_aliases.json').write_text(json.dumps(a,indent=2)+'\n')
key=len(list(E.glob('RPz4_resolution-round*.json')))+1
(E/f'RPz4_resolution-round{key}.json').write_text(json.dumps({'names':out,'records':records},indent=2)+'\n')
for n,v in out.items():print(n,'objects',len(v['objects_in_order']),'source matches',[(r['path'],r['sha256'][:12]) for r in v['source_matches']])
