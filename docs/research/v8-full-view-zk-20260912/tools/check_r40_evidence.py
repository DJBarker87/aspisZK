#!/usr/bin/env python3
"""Gate the model-linked M31 witness, not a source probability/privacy claim."""
import ast,hashlib,json,re
from pathlib import Path
root=Path(__file__).resolve().parent.parent;e=root/'evidence/r40-residual-nonzero';prior=root/'evidence/r39-point-weight-certificate'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((e/'MANIFEST.json').read_text())
for n,h in manifest.items():assert sha(e/n)==h,n
receipt=json.loads((e/'receipt.json').read_text());assert receipt['source_pins']==195 and receipt['new_lean_declarations']==481
assert receipt['nonzero_kernel_certificate']and receipt['coefficient_ring']=='ZMod 2147483647'
assert not any(receipt[k]for k in['source_distribution_bound','full_privacy','verifier_changed'])
m=json.loads((e/'r18-stage.json').read_text());old=json.loads((prior/'r18-stage.json').read_text());ex='docs/research/v8-no-work-100-20260907/experiments/'
assert receipt['source_manifest_sha256']==sha(e/'r18-stage.json')and len(m['files'])==195
assert m['r40_generator']['control_manifest_sha256']==sha(prior/'r18-stage.json')
for n,h in old['files'].items():
    if n!=ex+'performance-host/Cargo.toml':assert m['files'][n]==h,n
for n,h in m['files'].items():
    if(e/'source'/n).exists():assert sha(e/'source'/n)==h,n
assert sha(root/'tools/r40_entry_generator.rs')==m['files'][ex+'r40_entry_generator.rs']
runtime=json.loads((e/'runtime/metadata.json').read_text());assert runtime['source_manifest_sha256']==sha(e/'r18-stage.json')and runtime['overflow_checks']and len(runtime['generated'])==44
for n,h in runtime['generated'].items():assert sha(root/'lean/AspisV8R19'/n)==h,n
for label in['compile','write','check']:
    log=(e/f'runtime/{label}.log').read_text();assert '\tExit status: 0'in log and '\tSwaps: 0'in log
    if label!='compile':
        for s in['low_weight_checks=216','quotient_checks=1404','source_observation_checks=208','retained_minor_checks=169','slot_negative_columns=13']:assert s in log
raw=e/'runtime/retained-r37-minor.bin';assert sha(raw)==receipt['retained_r37_minor_sha256']==sha(root/'evidence/r37-source-restricted-residual/runtime/results/algebraic-witness-minor.bin')
matrix_source=(root/'lean/AspisV8R19/WitnessEntryData.lean').read_text().split('def matrix :',1)[1]
matrix=ast.literal_eval(re.search(r'\(\((\[.*\]) : List \(List Nat\)',matrix_source).group(1));flat=[v for row in matrix for v in row];assert len(flat)==169
assert b''.join(v.to_bytes(16,'little')for v in flat)==raw.read_bytes()
records=json.loads((e/'lean-f/metadata.json').read_text());assert len(records)==170
for r in records:assert r['exit']==0 and r['source_sha256']==sha(root/'lean'/(r['target_name']+'.lean'))and r['toolchain']=='leanprover/lean4:v4.32.0'
checks=[('a','ResidualEntryCertificate',2),('b','WitnessEntryData',0),('b','WitnessEntryInputs',3),('c','WitnessQuotient00',1),('d','WitnessEntryColumn00',34),('d','ResidualNonsingular',2),('d','WitnessQuotient12',1),('d','WitnessEntryColumn12',34),('d','WitnessInverseData',0),('d','WitnessInverseRow00',1),('e','WitnessEntryBridge',1),('f','WitnessNonzero',5)]
checks += [('e',f'WitnessQuotient{i:02}',1)for i in range(1,12)]
checks += [('e',f'WitnessEntryColumn{i:02}',34)for i in range(1,12)]
checks += [('e',f'WitnessInverseRow{i:02}',1)for i in range(1,13)]
assert sum(n for _,_,n in checks)==481
max_rss=0;wall_sum=0
for folder,name,count in checks:
    log=(e/f'lean-{folder}/{name}.log').read_text();assert 'sorryAx'not in log and log.count('depends on axioms:')==count and '\tExit status: 0'in log and '\tSwaps: 0'in log,name
    for ax in re.findall(r'depends on axioms: \[([^]]*)\]',log):assert set(ax.replace('\n',' ').replace(' ','').split(','))<={'propext','Classical.choice','Quot.sound'}
    max_rss=max(max_rss,int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',log).group(1)))
    time=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([\d:.]+)',log).group(1).split(':');wall_sum+=sum(float(x)*60**i for i,x in enumerate(reversed(time)))
for folder,name in [('b','WitnessQuotient00'),('c','WitnessEntryColumn00')]:
    failed=(e/f'lean-{folder}/{name}.log').read_text();assert 'Tactic `rewrite` failed'in failed and '\tExit status: 1'in failed
failed=(e/'lean-e/WitnessNonzero.log').read_text();assert 'Nontrivial M'in failed and '\tExit status: 1'in failed
for n in runtime['generated']:
    s=(root/'lean/AspisV8R19'/n).read_text()
    for bad in['native_decide','norm_num','sorry','maxRecDepth','rootRun']:assert bad not in s,(n,bad)
bridge=(root/'lean/AspisV8R19/WitnessNonzero.lean').read_text()
for s in['exact minor_matrix','matrix_right_inverse','assigned_det_ne_zero','ResidualNonsingular.polynomial_nonzero']:assert s in bridge
print(json.dumps({'status':'PASS','artifacts':len(manifest),'new_lean_declarations':481,'model_minor_entries':169,'inverse_product_entries':169,'lean_wall_seconds_sum':round(wall_sum,2),'lean_peak_rss_kib':max_rss,'coefficient_ring':'ZMod 2147483647','nonzero_kernel_certificate':True,'source_distribution_bound':False,'full_privacy':False},indent=2))
