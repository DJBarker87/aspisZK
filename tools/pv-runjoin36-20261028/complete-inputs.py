from pathlib import Path
import tomllib,json,subprocess,shlex,gzip,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin36-20261028';S='/home/dombarker/project-offloads/codex-pv-runjoin-20261026/runjoin36-extraction/input';seen=set()
def visit(p):
 p=p.resolve()
 if p in seen:return
 seen.add(p);x=tomllib.loads(p.read_text())
 for member in x.get('workspace',{}).get('members',[]):visit(p.parent/member/'Cargo.toml')
 def walk(d):
  if not isinstance(d,dict):return
  if 'path' in d and isinstance(d['path'],str) and (p.parent/d['path']/'Cargo.toml').is_file():visit(p.parent/d['path']/'Cargo.toml')
  for v in d.values():walk(v)
 walk(x)
visit(R/'Cargo.toml');visit(R/'tools/r1-cost-probe/Cargo.toml')
paths=set()
for p in seen:
 if p.parent==R:
  paths.update(['Cargo.toml','Cargo.lock']);continue
 for s in subprocess.check_output(['git','ls-tree','-r','--name-only','HEAD',str(p.parent.relative_to(R))],text=True).splitlines():
  if s.endswith(('.rs','.toml','.lock')):paths.add(s)
files={p:(R/p).read_text() for p in sorted(paths)}
code='''import pathlib,json,gzip,sys,hashlib
x=json.loads(gzip.decompress(sys.stdin.buffer.read()));s=pathlib.Path(x['source']);n=0
for p,b in x['files'].items():
 q=s/p
 if q.exists():assert q.read_bytes()==b.encode(),p
 else:q.parent.mkdir(parents=True,exist_ok=True);q.write_text(b);n+=1
print(json.dumps(dict(added=n,checked=len(x['files']))))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=gzip.compress(json.dumps(dict(source=S,files=files)).encode()),capture_output=True);assert r.returncode==0,r.stderr
x=json.load(open(E/'input-source-pins.json'));x['files'].update({p:hashlib.sha256(b.encode()).hexdigest() for p,b in files.items()});(E/'input-source-pins.json').write_text(json.dumps(x,indent=2)+'\n');print(len(seen),'manifests;',r.stdout.decode())
