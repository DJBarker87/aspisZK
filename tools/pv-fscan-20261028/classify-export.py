"""Archive only source/text receipts; validate frozen mirror and clean owned targets."""
from pathlib import Path
import json,lzma,hashlib,shutil
D=Path('/home/dombarker/project-offloads/codex-pv-fscan-20261028');O=D/'classify-export';O.mkdir(exist_ok=True)
source=json.loads((D/'runtime-source-pins.json').read_text());bad=[]
for x in source['files']:
 p=D/'src'/x['path'];h=hashlib.sha256(p.read_bytes()).hexdigest() if p.exists() else None
 if h!=x['sha256']:bad.append(dict(path=x['path'],expected=x['sha256'],actual=h))
assert not bad,bad
files={}
for parent in D.glob('classify-*'):
 if not parent.is_dir():continue
 for p in parent.iterdir():
  if p.is_file() and (p.name in ['metadata.json','inputs.json','command.json','results.json','Cargo.toml.txt','fixture.rs.txt','cargo-artifacts.jsonl']):
   b=p.read_bytes();files[str(p.relative_to(D))]=dict(sha256=hashlib.sha256(b).hexdigest(),size=len(b),text=b.decode())
for p in D.glob('classify-upload*.json'):
 b=p.read_bytes();files[p.name]=dict(sha256=hashlib.sha256(b).hexdigest(),size=len(b),text=b.decode())
# Retain every instrumented source suffix and shadow source, never compiled output.
for root in ['classification-vendor','classification-project-fixture','classification-dep-fixture','classification-zeroize']:
 for p in (D/root).rglob('*'):
  if p.is_file() and p.suffix in ['.rs','.toml','.lock']:
   b=p.read_bytes();files[str(p.relative_to(D))]=dict(sha256=hashlib.sha256(b).hexdigest(),size=len(b),text=b.decode())
with lzma.open(O/'captures.json.xz','wt') as f:json.dump(files,f)
removed=[]
p=D/'classification-target'
if p.exists():shutil.rmtree(p);removed.append(str(p))
(O/'integrity.json').write_text(json.dumps(dict(verified_runtime_files=len(source['files']),source_revision=source['revision'],source_mismatches=bad,removed_rebuildable_targets=removed,retained='all sources, fixture inputs, source diffs, metadata, command/output/timing/admission receipts; no wallet/key created or removed',archive_sha256=hashlib.sha256((O/'captures.json.xz').read_bytes()).hexdigest()),indent=2)+'\n')
print('verified runtime files',len(source['files']),'source mismatches',len(bad),'captured text files',len(files),'owned target cleaned')
