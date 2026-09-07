"""Review adapter: compare an externally supplied package with production-field Rust.

Usage: python3 zip_crosscheck.py /path/to/extracted/package /tmp/aspis-v8-chord-link
The package is not copied into the repository or uploaded by this script.
"""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

package=Path(sys.argv[1])
spec=importlib.util.spec_from_file_location('reviewed_chord',package/'structured_chord.py')
module=importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
rows=[json.loads(line) for line in subprocess.check_output([sys.argv[2],'--cross-fixture'],text=True).splitlines()]
assert len(rows)==40
def sample(n):return (n,n+1,n+2,n+3)
for row in rows:
    seed=row['case']
    pairs=[[sample(seed+10*j),sample(seed+10*j+1)] for j in range(10)]
    if seed%2==0:pairs[seed%10][0]=module.Z
    alpha=[sample(seed+30*j+1) for j in range(4)]
    if seed==0:alpha=[module.Z]*4
    if seed==1:alpha=[module.ONE]*4
    if seed==2:alpha=[(module.P-1,0,0,0),module.Z,module.ONE,(module.P-1,0,0,0)]
    chord=[sample(seed+401),sample(seed+501),sample(seed+601)]
    if 10<=seed<13:chord[seed-10]=module.Z
    outer=sample(seed+701)
    fast=module.transformed_product_terminal(pairs,outer,chord,alpha)
    dense=module.dual_fold(module.transpose_dense(module.dense_product(pairs,outer),chord),alpha)
    assert fast==dense==[tuple(v) for v in row['values']],seed
    assert row['products_including_outer_scale']==91
print('PASS 40 cross-language full-dimension cases / 160 terminal QM31 values: package fast = package dense = production-field Rust')
print('Rust count: 91 generic products including challenge powers and outer scale; not CU or a whole-verifier comparison')
