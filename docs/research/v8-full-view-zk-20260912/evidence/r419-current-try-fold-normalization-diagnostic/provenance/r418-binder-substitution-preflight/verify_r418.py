#!/usr/bin/env python3
"""Verify saved R418 source copies and decoded reference census; no mutation."""
from pathlib import Path
import hashlib, json
HERE=Path(__file__).resolve().parent
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((HERE/'source-manifest.json').read_text())
for row in manifest['files']:
    p=HERE/row['saved_path']
    assert p.is_file(), row['saved_path']
    assert sha(p)==row['sha256'], row['saved_path']
llbc=Path('/Users/dominic/ZK/.worktrees/ZK-v8-r21-public-arithmetic-20260922/docs/research/v8-full-view-zk-20260912/evidence/r405-generic-batch-translation-frontier/provenance/r396-private-batch-unmonomorphized-plan/R396PrivateBatchUnmonomorphized.llbc')
assert sha(llbc)==manifest['r396_decoded_reference_census']['target_input_sha256']
census=json.loads((HERE/'decoded-reference-census.json').read_text())
assert census['input']['sha256']=='399020435e94aaa7135c06d68445e9b936bd22fe6d1e1d197ee708d448d584ae'
assert len(census['direct_fun_decl_refs_id58'])==5
assert len(census['trait_dispatch_calls_method36'])==4
assert len(census['trait_method_impls'])==4
assert [r['fun_decl_id'] for r in census['function_binders_with_Try_Output_constraint']]==[58,120,169]
assert [r['arity']['types'] for r in census['direct_fun_decl_refs_id58']]==[5,5,6,5,5]
assert all(r['arity']['types']==3 for r in census['trait_dispatch_calls_method36'])
assert all(len(r['method_binder']['trait_type_constraints'])==1 for r in census['trait_method_impls'])
assert json.loads((HERE/'inventory.json').read_text())['input']['sha256']==census['input']['sha256']
remote=HERE/'remote-workspace'
for row in json.loads((remote/'pinned-charon-source/file-manifest.json').read_text())['files']:
    assert sha(remote/'pinned-charon-source'/row['path'])==row['sha256'], row['path']
workspace=json.loads((remote/'report.json').read_text())
assert workspace['host']['pinned_charon_checkout_head']=='cb50ff16b9f1066b8a97dc06da704de2da2fa41c'
assert workspace['tool']['sha256']=='b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c'
cache=json.loads((remote/'rustc-cache-report.json').read_text())
assert cache['toolchain']['rustc_commit']=='14210df0e27ccd7d9e6a05b8085cbd438e4bbc65'
assert cache['cached_artifacts'][0]['sha256']=='e7d6e9427a2d2a953bb2fe5dfe0bdc8d69bf1b2de7a224d2779e95ad502cc1c5'
sumfile=HERE/'SHA256SUMS'
if sumfile.exists():
    for line in sumfile.read_text().splitlines():
        expected, rel=line.split('  ',1)
        assert sha(HERE/rel)==expected, rel
print('R418 inventory checks passed: copied pinned source hashes and decoded R396 census counts/arity.')
