"""Read-only current effective environment and complete dependency-hash comparisons."""
import pathlib,json,subprocess,shlex,hashlib
R=pathlib.Path(__file__).resolve().parents[2];E=R/'evidence/pv-reach-20261027/resume10';P=E.parent/'resume7'
rows=json.loads((E.parent/'resume9/native-project-closure.json').read_text());external=json.loads((P/'external-object-manifest.json').read_text());head=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
for r in rows:
 if r['authority']=='h5':
  b=subprocess.check_output(['git','show',head+':'+r['path']]);assert hashlib.sha256(b).hexdigest()==r['sha256'],r['module'];r['revision']=head;r['blob']=subprocess.check_output(['git','rev-parse',head+':'+r['path']],text=True).strip()
(E/'project-closure.json').write_text(json.dumps(rows,indent=2)+'\n')
script='''import pathlib,json,sys,hashlib,re,os
x=json.load(sys.stdin);b=pathlib.Path('/home/dombarker/project-offloads');envs={'own':b/'codex-pv-reach-20261027/lean/J.json'};out={};hashes={}
def sha(p):
 if not p.is_file():return None
 k=str(p.resolve())
 if k not in hashes:hashes[k]=hashlib.sha256(p.read_bytes()).hexdigest()
 return hashes[k]
names={r['module'] for r in x['project']}|{r['module'].replace('/','.') for r in x['external']}
for key,p in envs.items():
 e=json.load(open(p));roots=[pathlib.Path(q) for q in e['LEAN_PATH'].split(':')];ds={}
 for m in sorted(names):
  rel=pathlib.Path(*m.split('.')).with_suffix('.olean');q=next((root/rel for root in roots if (root/rel).is_file()),None)
  ds[m]=dict(path=str(q),resolved_path=str(q.resolve()),sha256=sha(q)) if q else None
 out[key]=dict(environment_path=str(p),environment_sha256=sha(p),environment=e,objects=ds)
# IDs are inspected but never marked/consumed by this read-only preflight.
hits=[]
for root in b.glob('codex-pv-*'):
 for dp,dirs,files in os.walk(root):
  dirs[:]=[d for d in dirs if d not in ['target','target-charon','.git','node_modules']]
  for f in files:
   if re.search(r'(?<![0-9])404[0-9]{2}(?![0-9])',f):hits.append(str(pathlib.Path(dp)/f))
sent=b/'r1-privacy-build-integration-20261019/evidence/sent.txt'
out['id_preflight']=dict(range=[40400,40499],hits=hits,sent=[s for s in sent.read_text().splitlines() if re.search(r'(?<![0-9])404[0-9]{2}(?![0-9])',s)] if sent.exists() else [])
print(json.dumps(out,indent=2))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(script)],input=json.dumps(dict(project=rows,external=external)),capture_output=True,text=True,check=True)
(E/'environment-fingerprints.json').write_text(r.stdout);d=json.loads(r.stdout);own=d['own']['objects']
h4=[dict(module=r['module'],expected=r['object_sha256'],actual=own.get(r['module'].replace('/','.'),{})) for r in external if not own.get(r['module'].replace('/','.')) or own[r['module'].replace('/','.')]['sha256']!=r['object_sha256']]
(E/'h4-verification.json').write_text(json.dumps(dict(checked=len(external),mismatches=h4),indent=2)+'\n')
(E/'id-preflight.json').write_text(json.dumps(d['id_preflight'],indent=2)+'\n')
print('h4 mismatches',len(h4),'ids',d['id_preflight'],'own project missing',sum(own[r['module']] is None for r in rows))
