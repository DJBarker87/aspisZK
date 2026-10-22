#!/usr/bin/env python3
from pathlib import Path
import json,re,statistics,hashlib,sys,collections
h=Path(sys.argv[1]);out=Path(sys.argv[2]);out.mkdir(parents=True,exist_ok=True)
rows={};raw={};identities=[]
for stage in ['baseline','step1']:
 r=h/('pr1-'+stage)
 raw[stage]=[list(map(float,x.split())) for x in re.findall(r'^PR1_TIME (.*)$',(r/'receipts'/('pr1-'+stage+'-fixtures')/'stderr.log').read_text(),re.M)]
 assert len(raw[stage])==6
 records=[]
 for i in range(3):
  for w in ['transfer','withdrawal']:
   d=r/'fixtures'/f'S2-{w}-{i}';value=json.loads((d/'fixture.json').read_text());value['run']=i
   if stage=='step1':
    b=h/'pr1-baseline/fixtures'/d.name
    for f in ['proof.bin','public.bin']:
     assert (d/f).read_bytes()==(b/f).read_bytes()
     identities.append({'fixture':w,'run':i,'file':f,'sha256':hashlib.sha256((d/f).read_bytes()).hexdigest(),'bytes':(d/f).stat().st_size})
   records.append(value)
 rows[stage]={w:{'end_to_end_median_seconds':statistics.median([x['prover_wall_seconds'] for x in records if x['fixture']==w]),'p_r1_phase_subtotal_median_seconds':statistics.median([sum(x) for x in raw[stage][offset::2]]),'p_r1_total_seconds':None} for offset,w in enumerate(['transfer','withdrawal'])}
 (out/(stage+'-fixtures.json')).write_text(json.dumps(records,indent=2)+'\n')
a=json.loads((h/'pr1-baseline/challenges.json').read_text());b=json.loads((h/'pr1-step1/challenges.json').read_text());assert len(a)==len(b)==1000
for x,y in zip(a,b):
 assert (x['id'],x['case'],x['input_sha256'],x['accepted'])==(y['id'],y['case'],y['input_sha256'],y['accepted'])
elf=json.loads((h/'pr1-step1/elf-identities.json').read_text());assert len(elf)==3 and all(x['byte_equal'] for x in elf)
kani=(h/'pr1-step1/receipts/pr1-step1-kani-single-step/stdout.log').read_text();assert '3 successfully verified harnesses, 0 failures' in kani
result={'measurement_only':True,'timings':rows,'p_r1_timing_caveat':'Stage 1 records the sum of public_data/emit/builders/check durations. Parent catch/cleanup/drop overhead was not separately timed; this is a phase subtotal, not a claimed complete P_R1 wall measurement. End-to-end proof timers are complete.','baseline_caveat':'Baseline first pair overlapped optimized candidate compilation. Later samples were unpinned on a shared hybrid CPU; n=3 does not establish a statistically significant effect. Candidate first sample overlapped the initial Kani attempt.','fixture_identity':identities,'elf_identities':elf,'differential':{'sets':1000,'seed':'525f315f20261022','counts':dict(collections.Counter(x['case'] for x in a)),'accepted':sum(x['accepted'] for x in a),'rejected':sum(not x['accepted'] for x in a),'mismatches':0,'coverage_limit':'Four independent canonical accepting challenge sets; the other 996 sets randomize challenges but deliberately target duplicate/out-of-range query, HalfOK and zero-alpha rank rejection. Not uniform sampling, not exhaustive or a universal proof.'},'kani':'Three source-bound per-step projection/expected-overflow harnesses; no unbounded allocation or whole-P_R1 equivalence theorem','new_workers':0,'max_existing_lane_workers':12,'existing_unit_functional_workers':4,'arithmetic_workers':1,'target_met':False}
(out/'summary.json').write_text(json.dumps(result,indent=2)+'\n')
for stage,v in [('baseline',a),('step1',b)]: (out/(stage+'-challenges.json')).write_text(json.dumps(v,indent=2)+'\n')
print(json.dumps(rows,indent=2))
