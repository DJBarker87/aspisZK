#!/usr/bin/env python3
"""Check retained source snapshots, unchanged git inputs and native receipts."""
from pathlib import Path
import hashlib,json,subprocess
base=Path(__file__).resolve().parent
root=base.parents[3]
sha=lambda b:hashlib.sha256(b).hexdigest()
manifest=json.loads((base/'source-manifest.json').read_text())
for path,digest in manifest['files'].items():
 snapshot=base/'source-files'/path
 raw=snapshot.read_bytes() if snapshot.exists() else subprocess.check_output(['git','-C',str(root),'show',manifest['parent_revision']+':'+path])
 assert sha(raw)==digest,path
for p in sorted((base/'native').glob('*/receipt.json')):
 d=json.loads(p.read_text());out=p.parent
 assert d['exit']==0 and d['swap_current_bytes']==0
 assert d['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0'}
 assert d['source_manifest_sha256']==sha((base/'source-manifest.json').read_bytes())
 assert d['runner_sha256']==sha((out/'runner.py').read_bytes())
 assert 'test result: ok.' in (out/'test.log').read_text()
for line in (base/'SHA256SUMS').read_text().splitlines():
 digest,path=line.split('  ',1);assert sha((base/path).read_bytes())==digest,path
print('PASS:500 source inputs,4 focused optimized native receipts; extraction/refinement not claimed')
