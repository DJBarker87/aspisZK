#!/usr/bin/env python3
"""Freeze just the changed R119/R120 leaves, not a package-wide rebuild."""
import argparse,hashlib,json,re
from pathlib import Path
from generate_r120_certificate import make
p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args()
root=Path(__file__).resolve().parent.parent
inputs=root/'evidence/r120-augmented-section/source-results'
generated=make(json.loads((inputs/'source-weights.json').read_text()),json.loads((inputs/'high_code_support_pivot_check.json').read_text()))
names=['AugmentedQuerySection','AugmentedQuotient']+[n.removesuffix('.lean') for n in generated]+[
    'TwoSwapQueryTransport','AugmentedMaskTransport','AugmentedOpeningBoundary']
assert len(names)==len(set(names))==42
seen=set();records=[]
for name in names:
    f=root/'lean/AspisV8R19'/(name+'.lean');s=f.read_text()
    if name+'.lean' in generated:assert s==generated[name+'.lean']
    assert not re.search(r'\b(sorry|admit|native_decide)\b|^\s*axiom\s',s,re.M),name
    for module in re.findall(r'^import AspisV8R19\.(\w+)$',s,re.M):
        if module in names:assert module in seen,(name,module)
    seen.add(name);records.append({'target':'AspisV8R19/'+name,'sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'axioms_audits':len(re.findall(r'^#print axioms ',s,re.M))})
d={'base_revision':'3a4a95e8a5f6d5ee1369c37ae6485ea2b32bf757','toolchain':'leanprover/lean4:v4.32.0','targets':records,
   'generator_checked':True,'generic_leaves_preflighted':True,'exceptional_chunks_preflighted':True,
   'no_query_recurrence_kernel_reduction':True,'next_bridge':'TwoSwapQueryTransport.normalized_det_ne_zero',
   'source_refinement':False,'full_security':False}
out=Path(__file__).with_name('r120-release-manifest.json')
if a.check:assert json.loads(out.read_text())==d
else:assert not out.exists();out.write_text(json.dumps(d,indent=2)+'\n')
print(json.dumps({'status':'PASS','targets':len(records),'axioms_audits':sum(r['axioms_audits']for r in records)}))
