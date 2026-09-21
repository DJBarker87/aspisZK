#!/usr/bin/env python3
"""Same selected R18 profile: fixed half powers use the base field.

No new mask, randomness, permutation or transcript; compare to retained
extension-field scalar reference before SBF measurement.
"""
import argparse,hashlib,json,shutil
from pathlib import Path
from reconstruct_generated_inputs import EXPERIMENTS
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--stage',type=Path,required=True)
p.add_argument('--output',type=Path,required=True)
a=p.parse_args();assert not a.output.exists()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
meta=json.loads((a.stage/'r18-stage.json').read_text())
assert meta['compact_primary']
for name,expected in meta['files'].items():assert sha(a.stage/name)==expected,name
shutil.copytree(a.stage,a.output);root=a.output/EXPERIMENTS
repo=Path(__file__).resolve().parents[4]
path=root/'r18_sparse_coded_g.rs';before=sha(path)
shutil.copy2(repo/'tools/r18_sparse_coded_g.rs',path)
shutil.copy2(repo/'tools/r18_sparse_coded_g_check.rs',root/'r18_sparse_coded_g_check.rs')
meta['base_coin_scaling']={'before_sha256':before,'after_sha256':sha(path)}
meta['files'].update({str(p.relative_to(a.output)):sha(p) for p in sorted(root.glob('*.rs'))})
meta['sbf_measured']=False
(a.output/'r18-stage.json').write_text(json.dumps(meta,indent=2)+'\n')
print(json.dumps({'stage':str(a.output),'profile':meta['profile'],'transcript_unchanged':True}))
