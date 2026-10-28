"""Read-only cache/hash/ID audit, then separately invoked own-cache cleanup."""
import pathlib,json,subprocess,shlex
R=pathlib.Path(__file__).resolve().parents[2];E=R/'evidence/pv-l1-20261028'
rs=[json.loads(p.read_text()) for p in E.glob('receipt-*.json')]
checks={}
for r in rs:
 if r['accepted']:
  for m,d in r['dependencies'].items():
   if d:checks[d['path']]=d['sha256']
for r in json.loads((E/'reuse.json').read_text())['reused']:
 checks['/home/dombarker/project-offloads/codex-pv-l1-20261028/objects/'+r['module'].replace('.','/')+'.olean']=r['object_sha256']
for r in json.loads((E/'external-authority.json').read_text()):checks[r['path']]=r['object_sha256']
code=r'''import pathlib,json,sys,hashlib,os,re,datetime
checks=json.load(sys.stdin);mismatches=[]
for n,s in checks.items():
 p=pathlib.Path(n);actual=hashlib.sha256(p.read_bytes()).hexdigest() if p.is_file() else None
 if actual!=s:mismatches.append(dict(path=n,expected=s,actual=actual))
root=pathlib.Path('/home/dombarker/project-offloads');own=root/'codex-pv-l1-20261028';hits=[];dirs=0
pat=re.compile(r'(^|[-_])(516[0-9]{2})([-_.]|$)')
prune={'.git','target','objects','lean-objects','sources','external','node_modules','.lake','retained-objects','lean-objects2','__pycache__'}
for job in root.glob('codex-pv-*'):
 if job==own:continue
 for here,children,files in os.walk(job,followlinks=False):
  children[:]=[n for n in children if n not in prune];dirs+=1
  for n in files:
   if pat.search(n):hits.append(str(pathlib.Path(here)/n))
sent=root/'r1-privacy-build-integration-20261019/evidence/sent.txt'
sent_hits=[l for l in sent.read_text().splitlines() if re.search(r'\b516[0-9]{2}\b',l)]
objects=[]
for p in sorted((own/'objects').rglob('*.olean')):
 objects.append(dict(path=str(p.relative_to(own)),symlink=p.is_symlink(),size=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
result=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),checked_paths=len(checks),mismatches=mismatches,other_job_directories_scanned=dirs,other_id_hits=hits,sent_hits=sent_hits,objects=objects,all_match=not mismatches and not hits and not sent_hits)
(own/'evidence/final-cache-id-check.json').write_text(json.dumps(result));print(json.dumps(result))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(checks),capture_output=True,text=True)
assert r.returncode==0,r.stderr
(E/'final-cache-id-check.json').write_text(r.stdout);d=json.loads(r.stdout);assert d['all_match'],{k:v for k,v in d.items() if k!='objects'}
print('Hash paths:',d['checked_paths'],'Own objects:',len(d['objects']),'ID collisions:',len(d['other_id_hits']))
