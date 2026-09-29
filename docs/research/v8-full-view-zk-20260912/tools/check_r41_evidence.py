#!/usr/bin/env python3
"""Offline lift/degree gate. Source inspection is not a sampler-law proof."""
import hashlib,json,re
from pathlib import Path
root=Path(__file__).resolve().parent.parent;e=root/'evidence/r41-qm31-residual';prior=root/'evidence/r40-residual-nonzero'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((e/'MANIFEST.json').read_text())
for n,h in manifest.items():assert sha(e/n)==h,n
receipt=json.loads((e/'receipt.json').read_text());assert receipt['source_pins']==195 and receipt['new_lean_declarations']==34 and receipt['total_degree_bound']==1105
assert not any(receipt[k]for k in['source_runtime_rerun','source_distribution_bound','full_privacy','verifier_changed'])
assert receipt['source_manifest_sha256']==sha(e/'r18-stage.json')==sha(prior/'r18-stage.json')
m=json.loads((e/'r18-stage.json').read_text())
for n in receipt['inspected_source_files']:assert sha(e/'source'/n)==m['files'][n],n
records=json.loads((e/'lean-f/metadata.json').read_text());assert len(records)==176
for r in records:assert r['exit']==0 and r['source_sha256']==sha(root/'lean'/(r['target_name']+'.lean'))and r['toolchain']=='leanprover/lean4:v4.32.0'
checks=[('b','ResidualFieldLift',3),('b','QM31ResidualWitness',8),('d','ResidualDegree',18),('e','SourceResidualDegree',3),('f','QM31ResidualBoundary',2)]
assert sum(n for _,_,n in checks)==34
max_rss=0;wall_sum=0
for folder,name,count in checks+[('b','ExactTowerBase',1)]:
    log=(e/f'lean-{folder}/{name}.log').read_text();assert 'sorryAx'not in log and log.count('depends on axioms:')==count and '\tExit status: 0'in log and '\tSwaps: 0'in log,name
    for ax in re.findall(r'depends on axioms: \[([^]]*)\]',log):assert set(ax.replace('\n',' ').replace(' ','').split(','))<={'propext','Classical.choice','Quot.sound'}
    max_rss=max(max_rss,int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',log).group(1)))
    time=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([\d:.]+)',log).group(1).split(':');wall_sum+=sum(float(x)*60**i for i,x in enumerate(reversed(time)))
for folder,name in [('a','ResidualFieldLift'),('c','ResidualDegree')]:
    failed=(e/f'lean-{folder}/{name}.log').read_text();assert 'error'in failed and '\tExit status: 1'in failed
for _,name,_ in checks:
    s=(root/f'lean/AspisV8R19/{name}.lean').read_text()
    for bad in['native_decide','sorry','axiom ','maxRecDepth','norm_num']:assert bad not in s,(name,bad)
lift=(root/'lean/AspisV8R19/QM31ResidualWitness.lean').read_text();assert 'WitnessEntryData.assigned_det_ne_zero'in lift and 'ExactTowerBase'in lift and 'embedded_half'in lift
degree=(root/'lean/AspisV8R19/SourceResidualDegree.lean').read_text();assert 'minor_totalDegree (polyMinor half quarter) 85'in degree
ex=e/'source/docs/research/v8-no-work-100-20260907/experiments'
relation=(ex/'r17_host_relation.rs').read_text();schedule=(ex/'relation_callback.rs').read_text();gamma=(ex/'inactive_row_binding.rs').read_text();transcript=(e/'source/crates/aspis-core/src/transcript.rs').read_text()
assert 'challenge_queries_without_replacement(22,1<<18,64)'in schedule
assert schedule.index('p.t.absorb(label::V6_FINAL256')<schedule.index('challenge_queries_without_replacement(22,1<<18,64)')
suffix=relation.split('pub(super) fn verify_cached',1)[1];assert suffix.index('channel_challenge(')<suffix.index('absorb_round(')<suffix.index('let a=sample(')<suffix.index('query_schedule(')
assert 'for _ in 0..3' in gamma and 'if z!=s'in gamma
for s in['pub const CHALLENGE_RETRY_LIMIT: u32 = 8','pub const NONZERO_QM31_RETRY_LIMIT: u32 = 3','pub const CIRCLE_POINT_RETRY_LIMIT: u32 = 3','if !out.contains(&candidate)']:assert s in transcript
print(json.dumps({'status':'PASS','artifacts':len(manifest),'new_lean_declarations':34,'retained_tower_audited':True,'lean_wall_seconds_including_tower':round(wall_sum,2),'lean_peak_rss_kib':max_rss,'qm31_nonzero_certificate':True,'total_degree_bound':1105,'source_distribution_bound':False,'full_privacy':False},indent=2))
