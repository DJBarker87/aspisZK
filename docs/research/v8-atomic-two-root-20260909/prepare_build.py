#!/usr/bin/env python3
"""Prepare a fresh task-owned NUC archive; never writes the predecessor copy."""
import hashlib, json, pathlib, shutil, subprocess
root = pathlib.Path(__file__).resolve().parents[3]
assert str(root) == '/home/dombarker/project-offloads/aspis-v8-atomic-two-root-20260909'
assert not (root/'.git').exists()
old = root.parent/'aspis-v8-performance-20260908.scS2Jz'
ex = root/'docs/research/v8-no-work-100-20260907/experiments'
own = pathlib.Path(__file__).resolve().parent
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
artifacts = {
 'verifier.so': ('sbf-complete-terminal-stack/aspis_v8_complete_sbf.so','3d07a23833bac533f791b7ce2d619f4cd40aff6e1b5314c3b43be596b38c15a3'),
 'pool.so': ('sbf-pool-zero-fast/aspis_pool.so','26a444033153177adc5a3b1c0c32477c12f655d1e27636563fbfc6c0604cc1e6'),
 'registry.so': ('sbf-selected-registry/aspis_registry.so','76f4c382de8c638084cd3c15d50398224e5ad377eeebfbc15d6f35a61f0f045d'),
 'double.so': ('sbf-complete/aspis_pair_forest_result_double.so','3693edf83f100ca90229a8aa0406182d71fd56b6480a1fa7366c4caff4ad5c29'),
 'baseline-driver': ('docs/research/v8-no-work-100-20260907/experiments/performance-svm/target/release/aspis-v7-pair-forest-combined-rejection','7e4160da049f9dd60ffbc47522a2e005dfde23920acf9d5e05d5d2c8ca343e39'),
}
out = root/'artifacts'; out.mkdir(exist_ok=True)
record = {'base':'4aaa61e679189b2cf76bfc25c2e3ff8d5c76341e','artifacts':{},'source_overlays':[]}
for name,(path,expected) in artifacts.items():
    assert digest(old/path)==expected, path
    shutil.copy2(old/path,out/name)
    assert digest(out/name)==expected
    record['artifacts'][name]={'source':str(old/path),'sha256':expected,'bytes':(out/name).stat().st_size}
# Only the authenticated complete integration/profile and its driver controls
# are needed. The cached verifier/Pool ELFs remain immutable and hash pinned.
driver=root/'results/v7-pair-forest-combined-rejection-litesvm-20260828/harness/src/main.rs'
already_patched=digest(driver)=='264cab184d72b27e8945235041c9f74993bdc6462165f729ab95276850a85957'
if not already_patched:
    source_lock=json.loads((own/'evidence/archive-source.json').read_text())
    assert source_lock['base']==record['base']
    for name,expected in source_lock['files'].items():
        assert digest(root/name)==expected, 'Pinned source mismatch: '+name
for name in ['complete-integration','complete-matched-driver','pool-zero-driver','token-control-driver']:
    patch=ex/(name+'.patch')
    args=['git','apply','--unidiff-zero','--recount',str(patch)]
    if not already_patched:
        subprocess.run(args[:2]+['--check']+args[2:],cwd=root,check=True)
        subprocess.run(args,cwd=root,check=True)
    record['source_overlays'].append({'patch':name,'sha256':digest(patch)})
driver=root/'results/v7-pair-forest-combined-rejection-litesvm-20260828/harness/src/main.rs'
assert digest(driver)=='264cab184d72b27e8945235041c9f74993bdc6462165f729ab95276850a85957'
record['baseline_driver_source_sha256']=digest(driver)
fixtures=root/'fixtures';fixtures.mkdir(exist_ok=True)
expected=json.loads((ex.parent/'terminal-query-results.json').read_text())
for shape in ['transfer-13','transfer-255']:
    for i,case in enumerate(expected['maximum']['shapes'][shape],1):
        src=old/f'complete-max-{shape}-v1/proofs/proof-{i}.bin'
        # Stored fixture is the raw body; the harness prepends its candidate afterstate.
        assert digest(src)==case['proof_sha256']
        shutil.copy2(src,fixtures/f'{shape}-{i}.bin')
for target in ['performance-svm/target','performance-sbf/target']:
    source=old/'docs/research/v8-no-work-100-20260907/experiments'/target
    dest=ex/target
    assert not dest.exists()
    # Reflink if supported, otherwise independent copy; NEVER hard-link caches.
    subprocess.run(['cp','-a','--reflink=auto',str(source),str(dest)],check=True)
    record.setdefault('cache_copies',[]).append({'source':str(source),'destination':str(dest),'reuse':'Cargo fingerprints; paths changed; offline locked rebuild'})
(own/'evidence').mkdir(exist_ok=True)
(own/'evidence/artifact-provenance.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record,indent=2))
