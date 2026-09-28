#!/usr/bin/env python3
"""Offline source/receipt gate, not an unchanged full proof replay."""
import hashlib,json
from pathlib import Path
root=Path(__file__).resolve().parent.parent;e=root/'evidence/r33-admissible-g-residual'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((e/'MANIFEST.json').read_text())
for n,h in manifest.items():assert sha(e/n)==h,n
r=json.loads((e/'receipt.json').read_text());assert r['source_pins']==188 and r['actual_prefixes']==2
assert not any(r[k]for k in['source_prefix_substituted','full_privacy','universal_residual_coverage','verifier_changed'])
m=json.loads((e/'r18-stage.json').read_text());old=json.loads((root/'evidence/r31-sparse-g-inverse/r18-stage.json').read_text());ex='docs/research/v8-no-work-100-20260907/experiments/'
assert r['source_manifest_sha256']==sha(e/'r18-stage.json')and len(m['files'])==188
assert m['r33_residual']['control_manifest_sha256']==sha(root/'evidence/r31-sparse-g-inverse/r18-stage.json')
for n,h in old['files'].items():
    if n!=ex+'performance-host/Cargo.toml':assert m['files'][n]==h,n
for n,h in m['files'].items():
    if(e/'source'/n).exists():assert sha(e/'source'/n)==h,n
assert sha(root/'tools/r33_g_residual.rs')==m['files'][ex+'r33_g_residual.rs']
source=(root/'tools/r33_g_residual.rs').read_text();assert 'qcols[j][106..]'in source and 'original_schur[r][j],matrix[C+r][j]'in source
runtime=json.loads((e/'runtime/metadata.json').read_text());assert runtime['source_manifest_sha256']==sha(e/'r18-stage.json')and runtime['overflow_checks']and not runtime['source_prefix_substituted']
compile_log=(e/'runtime/compile.log').read_text();assert '\tExit status: 0'in compile_log and '\tSwaps: 0'in compile_log
selected=json.loads((root/'evidence/r31-sparse-g-inverse/runtime/result/summary.json').read_text())['columns']
for w in range(2):
    assert sha(e/f'prefix/world{w}.bin')==m['r28_h1_capacity']['prefixes'][w]['prefix_sha256']
    s=json.loads((e/f'runtime/world{w}/summary.json').read_text());assert s['selected_columns']==selected
    assert [s[k]for k in['core_rank','free_columns','residual_rows','residual_rank','target_basis','original_equations','negative_controls','changed_residual_rhs_entries']]==[271,428,17,13,276,79488,276,4320]
    assert s['residual_pivot_columns']==list(range(13))and s['residual_pivot_rows']==[1,2,3,4,5,6,7,8,10,11,12,13,15]
    assert s['actual_ood_parameters_checked']and s['four_source_dependencies_per_column']and not s['universal_residual_coverage']and not s['full_privacy']
    assert s['right_inverse_bytes']==3086784 and(e/f'runtime/world{w}/residual-minor.bin').stat().st_size==2704
    log=(e/f'runtime/world{w}.log').read_text();assert '\tExit status: 0'in log and '\tSwaps: 0'in log
records=json.loads((e/'lean-c/metadata.json').read_text());assert len(records)==16
for r in records:assert r['exit']==0 and r['source_sha256']==sha(root/'lean'/(r['target_name']+'.lean'))and r['toolchain']=='leanprover/lean4:v4.32.0'
for folder,name,count in [('a','NormalizedChord',4),('a','SparseGAdmissible',4),('a','PosteriorElimination',2),('a','GResidualSchur',2),('b','LowKernelSeparation',5),('b','LowGResidualSupport',4),('c','SourceEdgeGrowth',5)]:
    log=(e/f'lean-{folder}/{name}.log').read_text();assert 'sorryAx'not in log and log.count('depends on axioms:')==count and '\tExit status: 0'in log and '\tSwaps: 0'in log
print(json.dumps({'status':'PASS','artifacts':len(manifest),'new_lean_declarations':15,'actual_prefixes':2,'source_reconstructions':552,'low_core_zero_residual_columns':13,'residual_rank_per_prefix':13,'universal_residual_coverage':False,'full_privacy':False,'verifier_changed':False},indent=2))
