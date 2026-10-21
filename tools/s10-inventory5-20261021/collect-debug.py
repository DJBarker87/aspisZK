#!/usr/bin/env python3
"""Collect bounded receipts and pins; never commit diagnostic ELFs/large data."""
import hashlib,json,subprocess
from pathlib import Path
R=Path(__file__).resolve().parents[2];E=R/'docs/research/100bit-spend-path-20261013/evidence/s10-inventory5-20261021'
H='/home/dombarker/project-offloads/codex-cx-s10-inventory5-20261021';REMOTE='dombarker@100.108.41.90'
def fetch(remote,local):subprocess.run(['scp','-q',REMOTE+':'+H+'/'+remote,str(local)],check=True,timeout=60)
for v in ['1','2']:
    base='build-default-v'+v
    for name in ['command.json','artifact-comparison.json','reservation.json','receipt/receipt.json','receipt/time.log','receipt/stdout.log','receipt/stderr.log']:
        fetch(base+'/'+name,E/(base+'-'+name.replace('/','-')))
fetch('debug-comparisons.json',E/'debug-comparisons.json')
manifest=dict(schema='s10-pass5-debug-builds-v1',analysis_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),
    model='OraclePortFrozen2.dV_frozen2',
    result='TRANSFER_REFUSED: executable/allocated section equality fails for full-debug and line-tables-only variants. No final inline witness is adopted.',
    print_axioms='N/A: diagnostic optimized SBF builds and byte comparisons, no source-refinement theorem',
    generators={str(p.relative_to(R)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [R/'tools/s10-inventory5-20261021/debug-build-host.py',R/'tools/s10-inventory5-20261021/debug-compare-host.py',R/'tools/s10-inventory5-20261021/rustc-debug.py',R/'tools/s10-inventory5-20261021/historical/rustc-debug-full.py']},
    receipts={str(p.relative_to(E)):hashlib.sha256(p.read_bytes()).hexdigest() for p in E.glob('build-default-v*')})
(E/'debug-build-manifest.json').write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n')
print(manifest['result'])
