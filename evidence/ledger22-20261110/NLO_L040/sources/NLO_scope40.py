"""Read-only retention and full source/selected-object integrity check."""
from pathlib import Path
import json,lzma,hashlib,os,shutil,subprocess
B=Path.cwd();H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
seeds=json.loads((B/'NLO_SEED_INPUTS.json').read_text());cache=Path('/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NLO_20261110')
for r in seeds:assert H(cache/(r['tag']+'_seed')/r['relative'])==r['sha256']
exports=json.loads((B/'NLO_EXPORT.json').read_text())['files']
for r in exports:assert H(Path(r['path']))==r['sha256']
closure=json.loads(lzma.decompress((B/'NLO_CLOSURE_PINS.json.xz').read_bytes()))
for r in closure['selected_objects']:assert H(Path(r['path']))==r['sha256']
receipts=[]
for p in B.glob('NLO_L*/receipt.json'):
 if p.parent.name=='NLO_L040':continue
 r=json.loads(p.read_text())
 for n,h in r['source_hashes'].items():assert H(p.parent/'sources'/n)==h,(p,n)
 receipts.append(dict(attempt=r['attempt'],sources=len(r['source_hashes'])))
assert len(receipts)==39
out=dict(status='PASS',selected_objects_rehashed=len(closure['selected_objects']),modules=closure['modules'],seed_files_rehashed=len(seeds),exports_rehashed=len(exports),receipts=receipts,cache_retained=cache.exists(),TMPDIR_retained=Path(os.environ['TMPDIR']).is_dir(),deletions=0,disk=shutil.disk_usage(B)._asdict(),own_cache_bytes=int(subprocess.check_output(['du','-sb',str(cache)]).split()[0]),own_workspace_bytes=int(subprocess.check_output(['du','-sb',str(B)]).split()[0]))
(B/'NLO_FINAL_HOST.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps(out))
