"""Prepare frozen inputs and current pinned extractor; no source/backend edits."""
from pathlib import Path
import subprocess,json,hashlib,shlex,gzip
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin36-20261028';host='dombarker@100.108.41.90';H='/home/dombarker/project-offloads/codex-pv-runjoin-20261026';W=H+'/runjoin36-extraction';S=W+'/input'
rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
# Reuse the own source workspace; add only missing frozen files, never overwrite.
paths=subprocess.check_output(['git','ls-tree','-r','--name-only',rev,'crates','programs','tools/r1-cost-probe','Cargo.toml','Cargo.lock'],text=True).splitlines()
paths=[p for p in paths if p.endswith(('.rs','.toml','.lock'))];files={p:(R/p).read_text() for p in paths};pins={p:hashlib.sha256(b.encode()).hexdigest() for p,b in files.items()}
code='''import pathlib,json,sys,gzip,hashlib
x=json.loads(gzip.decompress(sys.stdin.buffer.read()));s=pathlib.Path(x['source']);w=pathlib.Path(x['workspace']);w.mkdir(exist_ok=True);assert not s.exists();s.mkdir();rows=[]
for p,b in x['files'].items():
 q=s/p;h=hashlib.sha256(b.encode()).hexdigest();exists=q.exists();old=hashlib.sha256(q.read_bytes()).hexdigest() if exists else None
 if exists and old!=h:raise RuntimeError(('frozen source mismatch',p,old,h))
 if not exists:q.parent.mkdir(parents=True,exist_ok=True);q.write_text(b)
 rows.append(dict(path=p,sha256=h,already_present=exists))
print(json.dumps(dict(source=str(s),workspace=str(w),files=rows)))
'''
r=subprocess.run(['ssh',host,'python3 -c '+shlex.quote(code)],input=gzip.compress(json.dumps(dict(source=S,workspace=W,files=files)).encode()),capture_output=True)
(E/'frozen-input-preparation-fresh.json').write_text(json.dumps(dict(exit=r.returncode,stdout=r.stdout.decode(),stderr=r.stderr.decode(),revision=rev),indent=2)+'\n');assert r.returncode==0,r.stderr
(E/'input-source-pins.json').write_text(json.dumps(dict(revision=rev,source=S,files=pins),indent=2)+'\n')
cmd='sha256sum '+H+'/../codex-pv-cb-20261026/pinned-tools/{charon,charon-driver,aeneas}'
r=subprocess.run(['ssh',host,cmd],capture_output=True,text=True);assert r.returncode==0,r.stderr
(E/'extractor-pins.txt').write_text(r.stdout)
assert 'daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8' in r.stdout
assert '562e1f51ef9bea84f62793f21b4d6b48f9ae65c61ec72588170b2c3abdc37f19' in r.stdout
print('verified',len(pins),'frozen inputs; unchanged Stream B pinned tools (evidence/pv-cb3-20261026/retained-extractor-pins.txt)')
