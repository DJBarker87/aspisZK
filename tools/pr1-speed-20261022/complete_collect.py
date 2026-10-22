#!/usr/bin/env python3
from pathlib import Path
import json,re,statistics,hashlib,sys,collections
h=Path(sys.argv[1]);out=Path(sys.argv[2]);out.mkdir(parents=True,exist_ok=True)
measurements={};resources={};byte_rows=[]
for stage in ['baseline','step1']:
 r=h/('pr1-'+stage);records=[];receipts=[]
 for run in range(3):
  d=r/'receipts'/f'pr1-{stage}-complete-{run}'
  rec=json.loads((d/'receipt.json').read_text());assert rec['exit_status']==0
  receipts.append(rec)
  times=[list(map(float,x.split())) for x in re.findall(r'^PR1_TIME (.*)$',(d/'stderr.log').read_text(),re.M)]
  assert len(times)==2 and all(len(x)==5 and x[4]>=sum(x[:4]) for x in times)
  for j,fixture in enumerate(['transfer','withdrawal']):
   p=r/f'fixtures-complete-{run}'/f'S2-{fixture}-0'
   md=json.loads((p/'fixture.json').read_text())
   for file in ['proof.bin','public.bin']:
    a=(p/file).read_bytes();b=(h/'pr1-baseline/fixtures'/f'S2-{fixture}-0'/file).read_bytes();assert a==b
    byte_rows.append({'stage':stage,'run':run,'fixture':fixture,'file':file,'sha256':hashlib.sha256(a).hexdigest(),'bytes':len(a)})
   records.append({'run':run,'fixture':fixture,'end_to_end_seconds':md['prover_wall_seconds'],'p_r1_seconds':times[j][4],'phases_seconds':dict(zip(['public_data','emit','builders','check'],times[j][:4])),'native_acceptance':md['native_acceptance'],'dense_acceptance':md['dense_acceptance']})
 measurements[stage]={'samples':records,'medians':{f:{k:statistics.median([x[k] for x in records if x['fixture']==f]) for k in ['end_to_end_seconds','p_r1_seconds']} for f in ['transfer','withdrawal']}}
 resources[stage]={'cpu':'Intel Core Ultra 7 155H, 16 physical cores / 22 logical CPUs','peak_rss_kib':max(x['peak_rss_kib'] for x in receipts),'swaps':sum(x['swaps'] for x in receipts),'thread_counts_sampled':sorted({t['threads'] for x in receipts for t in x['thread_samples']}),'cpus_sampled':sorted({t['last_cpu'] for x in receipts for t in x['thread_samples']}),'limits':receipts[0]['limits'],'new_workers':0,'existing_arithmetic_workers':1,'existing_public_data_workers':4,'existing_lane_workers':12,'max_lane_threads_including_caller':13}
helped={f:{k:measurements['step1']['medians'][f][k]<measurements['baseline']['medians'][f][k] for k in ['end_to_end_seconds','p_r1_seconds']} for f in ['transfer','withdrawal']}
result={'measurement_only':True,'method':'Three alternating baseline/candidate pairs, each pair contains deterministic transfer then withdrawal. Separate processes and capped scopes. All task compilation, Kani and challenge-corpus jobs completed before this comparison. No CPU pinning or machine isolation; shared-host scheduling and thermal/frequency effects remain.','measurements':measurements,'resources':resources,'byte_identity':byte_rows,'strict_median_improvement':helped,'stop_after_stage1':not all(all(x.values()) for x in helped.values()),'target_met':all(x['p_r1_seconds']<=10 and x['end_to_end_seconds']<15 for x in measurements['step1']['medians'].values()),'trust':'Functional fixture/corpus evidence plus source-bound per-step descriptor Kani; no whole-program equivalence, privacy, source-to-model composition, L2 transport or L3 proof. No new workers or delayed reductions.'}
(out/'complete-summary.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:result[k] for k in ['strict_median_improvement','stop_after_stage1','target_met']},indent=2));print(json.dumps({s:v['medians'] for s,v in measurements.items()},indent=2))
