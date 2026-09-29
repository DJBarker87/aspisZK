#!/usr/bin/env python3
"""Gate the new high witness; do not promote low-repair invariance to source privacy."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
root=Path(__file__).resolve().parent.parent;e=root/'evidence/r43-high-query-witness'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((e/'MANIFEST.json').read_text())
for n,h in manifest.items():assert sha(e/n)==h,n
receipt=json.loads((e/'receipt.json').read_text());assert receipt['new_lean_declarations']==39 and receipt['arbitrary_low_repair_invariance']
assert not any(receipt[k]for k in['universal_source_root_theorem','source_distribution_bound','full_privacy','verifier_changed','new_sbf_measurement'])
old=json.loads((e/'control/r18-stage.json').read_text());assert sha(e/'control/r18-stage.json')==sha(root/'evidence/r42-admissible-grid/query/r18-stage.json')
cargo='docs/research/v8-no-work-100-20260907/experiments/performance-host/Cargo.toml';ex='docs/research/v8-no-work-100-20260907/experiments/'
for letter in 'abcdefghi':
    m=json.loads((e/f'rust-{letter}/r18-stage.json').read_text());assert len(m['files'])==198
    for n,h in old['files'].items():
        if n!=cargo:assert m['files'][n]==h,n
    host='r43_query_coverage.rs'if letter<'f'else'r43_universal_witness.rs';assert m['files'][ex+host]==sha(e/f'rust-{letter}'/host)
    if letter in'ei':assert sha(e/f'rust-{letter}'/host)==sha(root/'tools'/host)
final=json.loads((e/'rust-i/r18-stage.json').read_text())
for f in(e/'source').glob('*.rs'):assert final['files'][ex+f.name]==sha(f)
records=json.loads((e/'lean-h/metadata.json').read_text());assert len(records)==197
for r in records:assert r['exit']==0 and r['source_sha256']==sha(root/'lean'/(r['target_name']+'.lean'))and r['toolchain']=='leanprover/lean4:v4.32.0'
checks=[('d','HighRepairInvariant',5),('f','SparseHighWitness',10),('g','HighWitnessData',0),('g','HighWitnessEntries',1)]+[('g',f'HighWitnessInverseRow{i:02}',1)for i in range(13)]+[('g','HighWitnessNonzero',3),('h','HighWitnessTransport',7)]
assert sum(n for _,_,n in checks)==39
def metrics(log):
    assert '\tExit status: 0'in log and '\tSwaps: 0'in log
    rss=int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',log).group(1));t=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([\d:.]+)',log).group(1).split(':')
    return sum(float(x)*60**i for i,x in enumerate(reversed(t))),rss
times=[]
for letter,name,count in checks:
    log=(e/f'lean-{letter}/{name}.log').read_text();assert 'sorryAx'not in log and log.count('depends on axioms:')==count
    for ax in re.findall(r'depends on axioms: \[([^]]*)\]',log):assert set(ax.replace('\n',' ').replace(' ','').split(','))<={'propext','Classical.choice','Quot.sound'}
    times.append(metrics(log));src=(root/f'lean/AspisV8R19/{name}.lean').read_text()
    for bad in['native_decide','sorry','axiom ','maxRecDepth','norm_num']:assert bad not in src,(name,bad)
failed=(e/'lean-e/HighWitnessEntries.log').read_text();assert failed.count('is false')==3 and '\tExit status: 1'in failed
for letter in'abcdefi':
    meta=json.loads((e/f'rust-{letter}/metadata.json').read_text());assert meta['overflow_checks'] and not meta['universal_rank'] and not meta['full_privacy']
    assert meta['source_manifest_sha256']==sha(e/f'rust-{letter}/r18-stage.json')
    assert all(c['exit']==0 for c in meta['commands']);assert '--release'in meta['commands'][0]['command']
    metrics((e/f'rust-{letter}/compile.log').read_text());metrics((e/f'rust-{letter}/coverage.log').read_text())
assert '\tExit status: 101'in(e/'rust-g/compile.log').read_text()
assert 'left: 4\n right: 3'in(e/'rust-h/coverage.log').read_text()
for letter,cases,needle in[('a',32,'selected13_rank=13'),('b',36,'full27_rank='),('c',32,'full27_rank=12'),('d',32,'full27_rank=12'),('e',32,'selected28_rank=13 full28_rank=13')]:
    lines=[s for s in(e/f'rust-{letter}/coverage.log').read_text().splitlines()if s.startswith('R43_QUERY_CASE ')];assert len(lines)==cases and all(needle in s for s in lines)
log=(e/'rust-i/coverage.log').read_text()
for s in['rank=13 determinant=2079196465','source_weight_checks=3072 low_functional_checks=256 omitted_boundary_negative=4','normalized_columns=112 observation_checks=1904 changed_low_coordinates=2440']:assert s in log
data=json.loads((e/'rust-i/results/witness.json').read_text());assert data['selected_kernel_columns']==list(range(6,18))+[29]and not data['universal_root_theorem']
assert sha(e/'rust-i/results/witness.json')==sha(e/'rust-f/results/witness.json')
subprocess.run([sys.executable,str(root/'tools/generate_r43_certificate.py'),'--input',str(e/'rust-i/results/witness.json'),'--output',str(root/'lean/AspisV8R19'),'--check'],check=True)
source=(root/'lean/AspisV8R19/SparseHighWitness.lean').read_text();assert '+5*hg'in source and 'half^10*chordEntry'in source
print(json.dumps({'status':'PASS','artifacts':len(manifest),'new_theorems':39,'lean_wall_seconds':round(sum(t for t,_ in times),2),'lean_peak_rss_kib':max(r for _,r in times),'fixed_matrix_nonzero':True,'arbitrary_low_repair_invariance':True,'universal_source_root_theorem':False,'full_privacy':False,'new_sbf_measurement':False},indent=2))
