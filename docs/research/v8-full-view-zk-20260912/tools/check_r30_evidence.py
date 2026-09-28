#!/usr/bin/env python3
"""Offline integrity gate, no repeated numerical or formal compilation."""
import hashlib,json
from pathlib import Path
root=Path(__file__).resolve().parent.parent;e=root/'evidence/r30-query-kernel'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((e/'MANIFEST.json').read_text())
for n,h in manifest.items():assert sha(e/n)==h,n
receipt=json.loads((e/'receipt.json').read_text());assert receipt['pins']==186 and not receipt['verifier_changed']and not receipt['source_prefix_substituted']and not receipt['full_privacy']
m=json.loads((e/'r18-stage.json').read_text());assert len(m['files'])==186 and receipt['source_manifest_sha256']==sha(e/'r18-stage.json')
control=json.loads((root/'evidence/r29-beta-uniform/capacity/r18-stage.json').read_text());ex='docs/research/v8-no-work-100-20260907/experiments/'
for n,h in control['files'].items():
    if n not in[ex+'performance-host/Cargo.toml',ex+'r28_source_helpers.rs']:assert m['files'][n]==h,n
for n,h in m['files'].items():
    p=e/'source'/n
    if p.exists():assert sha(p)==h,n
assert sha(root/'tools/r30_kernel_separation.rs')==m['files'][ex+'r30_kernel_separation.rs']
for w in range(2):
    assert sha(e/f'prefix/world{w}.bin')==m['r28_h1_capacity']['prefixes'][w]['prefix_sha256']
    s=json.loads((e/f'runtime/world{w}/summary.json').read_text())
    assert [s[x]for x in['low_basis_checks','low_support_max','active_min','kernel_columns','H_core_rank','H_residual_rank','G_core_rank','G_residual_rank']]==[264,90,91,699,214,8,271,13]
    assert len(s['H_pivot_columns'])==222 and len(s['G_pivot_columns'])==284
    assert s['point_negative_control']and not s['universal_rank_proved']and not s['full_privacy']
    log=(e/f'runtime/world{w}.log').read_text();assert 'core_coordinate_equalities=339015 raw_zero_checks=61512'in log and '\tExit status: 0'in log and '\tSwaps: 0'in log
records=json.loads((e/'lean/metadata.json').read_text());assert len(records)==2
for rec,leaf,count in zip(records,['AspisV8R17/SourceScatter','AspisV8R19/LowKernelSeparation'],[19,5]):
    assert rec['exit']==0 and rec['source_sha256']==sha(root/'lean'/(leaf+'.lean'))
    log=(e/'lean'/(Path(leaf).name+'.log')).read_text();assert 'sorryAx'not in log and log.count('depends on axioms:')==count and '\tSwaps: 0'in log
print(json.dumps({'status':'PASS','artifacts':len(manifest),'actual_prefixes':2,'large_query_independent_blocks':[214,271],'tested_residual_ranks':[8,13],'new_lean_leaves':5,'universal_rank_proved':False,'full_privacy':False,'verifier_changed':False},indent=2))
