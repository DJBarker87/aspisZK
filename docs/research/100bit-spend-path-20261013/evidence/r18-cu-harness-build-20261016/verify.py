#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,subprocess
base=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
summary=json.loads((base/'summary.json').read_text())
source=json.loads((base/'source-manifest.json').read_text())
for label,exit in [('a',101),('b',0)]:
 out=base/('attempt-'+label);r=json.loads((out/'receipt.json').read_text());m=json.loads((out/'harness-manifest.json').read_text())
 assert r['exit']==exit and r['swap_current_bytes']==0
 assert r['harness_manifest_sha256']==sha((out/'harness-manifest.json').read_bytes())
 assert r['source_manifest_sha256']==sha((base/'source-manifest.json').read_bytes())
 assert r['runner_sha256']==sha((out/'runner.py').read_bytes())
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0'}
 for p,digest in m['files'].items():assert sha(subprocess.check_output(['git','-C',str(base),'show',summary['source_revision']+':'+p]))==digest,p
for p,digest in source['files'].items():assert sha(subprocess.check_output(['git','-C',str(base),'show',summary['source_revision']+':'+p]))==digest,p
for line in (base/'SHA256SUMS').read_text().splitlines():
 digest,p=line.split('  ',1);assert sha((base/p).read_bytes())==digest,p
print('PASS: failed staging attempt retained; optimized harness build green; execution not claimed')
