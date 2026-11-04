from pathlib import Path
import subprocess,json,lzma,hashlib
E=Path(__file__).resolve().parent;H='/home/dombarker/project-offloads/codex-pv-k4trace-20261104'
# Read exact manifest/lock bytes; all hashes remain those of original K12.
cp=json.loads((E/'source-config.json').read_text())['C084']
paths=[cp['root']+'/'+p for p in ['cblib/Cargo.toml','cblib/Cargo.lock']]
code='from pathlib import Path;import json;print(json.dumps({p:Path(p).read_text() for p in '+repr(paths)+'}))'
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,capture_output=True,text=True);assert r.returncode==0,r.stderr
payload=json.loads(lzma.decompress((E/'source-payload.json.xz').read_bytes()));prov=json.loads((E/'source-provenance.json').read_text())
for p,s in json.loads(r.stdout).items():
 rel=p[len(cp['root'])+1:];assert hashlib.sha256(s.encode()).hexdigest()==cp['pins'][rel]
 payload['kstub/'+rel]=s;prov['kstub/'+rel]={'path':p,'sha256':cp['pins'][rel],'authority':'original K12 source-manifest.json'}
(E/'source-payload.json.xz').write_bytes(lzma.compress(json.dumps(payload).encode()));(E/'source-provenance.json').write_text(json.dumps(prov,indent=2)+'\n')
for src,dst in [('host_run.py','host_run.py'),('runs.json','runs.json'),('original/tools.json','tools.json'),('source-payload.json.xz','source-payload.json.xz')]:subprocess.run(['scp',str(E/src),'dombarker@100.108.41.90:'+H+'/'+dst],check=True,capture_output=True)
code='''from pathlib import Path
import json,lzma,hashlib
R=Path(ROOT)
p=json.loads(lzma.decompress((R/'source-payload.json.xz').read_bytes()))
for n,s in p.items():
 q=R/'sources'/n;q.parent.mkdir(parents=True,exist_ok=True)
 if q.exists():assert q.read_text()==s
 else:q.write_text(s)
(R/'tmp').mkdir(exist_ok=True)
print('restored verbatim',len(p),'source files')
'''.replace('ROOT',repr(H))
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,capture_output=True,text=True);assert r.returncode==0,r.stderr;print(r.stdout)
