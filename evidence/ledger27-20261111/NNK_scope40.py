"""Read-only final host retention/pin validation inside the last admitted scope."""
from pathlib import Path
import json,lzma,hashlib,shutil,os
B=Path.cwd();H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
closure=json.loads(lzma.decompress((B/'NNK_CLOSURE_PINS.json.xz').read_bytes()));pins=closure['selected_objects']
for r in pins:assert H(Path(r['path']))==r['sha256'],r['path']
seeds=json.loads((B/'NNK_SEED_INPUTS.json').read_text())
C=Path('/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NNK_20261111')
for r in seeds:
 assert H(Path(r['path']))==r['sha256']
 assert H(C/(r['tag']+'_seed')/r['relative'])==r['sha256']
exports=json.loads((B/'NNK_EXPORT.json').read_text())
for r in exports['files']:assert H(Path(r['path']))==r['sha256']
# Every completed attempt retains its exact source snapshot, including linker inputs.
checked=0
for q in sorted(B.glob('NNK_L[0-9][0-9][0-9]/receipt.json')):
 r=json.loads(q.read_text())
 for name,digest in r['source_hashes'].items():assert H(q.parent/'sources'/name)==digest,(q,name)
 checked+=1
imports=json.loads(lzma.decompress((B/'NNK_CACHE_IMPORTS.json.xz').read_bytes()))
rawbinary=next(r for r in imports['files'] if r['tag']=='raw-ax2-binary')
assert H(Path(rawbinary['destination']))==rawbinary['sha256']==H(Path(rawbinary['path']))
x=dict(status='PASS',selected_objects=len(pins),seed_files=len(seeds),exports=len(exports['files']),completed_source_snapshot_sets=checked,cache=str(C),cache_retained=True,TMPDIR_retained=(B/'NNK_tmp').is_dir(),deletions=0,workspace_disk=shutil.disk_usage(B)._asdict(),cache_bytes=sum(p.stat().st_size for p in C.rglob('*')if p.is_file()),workspace_bytes=sum(p.stat().st_size for p in B.rglob('*')if p.is_file()))
(B/'NNK_FINAL_HOST.json').write_text(json.dumps(x,indent=1)+'\n');print(json.dumps(x))
