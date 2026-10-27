"""Read-only receipt aggregation; never launches a validation."""
from pathlib import Path
import datetime,hashlib,json,re,subprocess
r=Path(__file__).resolve().parents[3];e=r/'evidence/pv-rw21-20261027'
rows=[json.loads(p.read_text()) for p in sorted(e.glob('37???-receipt.json'))]
lean=[x for x in rows if x.get('charged')]
keys=['attempt','module','target','exit_status','wall_time','peak_rss_kib','swaps','source_revision','source_sha256','deps_fingerprint','print_axioms']
formal=[{k:x.get(k) for k in keys} for x in lean]
keys=['attempt','target','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','print_axioms','cgroup_memory_peak_bytes','cgroup_swap_peak_bytes','rss_measurement','limits','expected_work']
native=[]
for p in sorted(e.glob('pv-rw21-kani-*/receipt.json')):
 x=json.loads(p.read_text());native.append({k:x.get(k) for k in keys})
standard={'propext','Classical.choice','Quot.sound'}
axioms=[a.strip() for x in lean if x['exit_status']==0 for line in x.get('print_axioms',[]) if 'depends on axioms: [' in line for a in line.split('depends on axioms: [')[1].split(']')[0].split(',')]
latest={x['module']:x for x in lean};checked=[];pending=[]
for p in sorted((r/'docs/research/v8-r0-zk-20261009/lean/R1Z').glob('ProverRw21*.lean')):
 module='R1Z.'+p.stem;x=latest.get(module);sha=hashlib.sha256(p.read_bytes()).hexdigest()
 (checked if x and x['exit_status']==0 and x['source_sha256']==sha else pending).append({'module':module,'source_sha256':sha,'attempt':x['attempt'] if x else None})
inputs=[json.loads(p.read_text()) for p in e.glob('37???-input.json')]
s=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),branch=subprocess.check_output(['git','branch','--show-current'],cwd=r,text=True).strip(),base='0242bd9221eb87dac8906ccbcac6d34ab1a9d2a2',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=r,text=True).strip(),lean_charged=len(lean),lean_remaining=100-len(lean),lean_passes=sum(x['exit_status']==0 for x in lean),lean_failures=sum(x['exit_status']!=0 for x in lean),kani_charged=len(native),next_unused_id=max(x['attempt'] for x in inputs)+1,checked_modules=checked,pending_modules=pending,all_successful_axioms_standard=set(axioms)<=standard,formal_attempts=formal,native_attempts=native,V164={'historical_before':['source_law','context_identity'],'resume_before':['P_source_p6'],'after':['P_source_p6'],'closed':False},V163={'whole_deployed_model_construction':'OPEN','transfer_fixture_proof_bytes':'OPEN','withdrawal_fixture_proof_bytes':'OPEN','general_proof_bytes':'OPEN','published_name':'R1Z.ProverRw21ModelInstance','published_name_scope':'mathematical transcript serializer, not yet deployed-input protocol construction'},endpoint_premises_removed=[],endpoint_premises_added=[],target_established=False,cache_scope='cached component replay, not clean-source rebuild',new_local_lean_compiles=0,source_counterexample_established=False,stop_reason='Lean budget exhausted' if len(lean)==100 else 'in progress')
(e/'summary.json').write_text(json.dumps(s,indent=2)+'\n')
with (e/'receipts.tsv').open('w') as f:
 f.write('attempt\ttarget\texit\twall\tpeak_rss_kib\tswap\tsource_revision\taxioms\n')
 for x in formal:f.write('\t'.join(str(v) for v in [x['attempt'],x['module'],x['exit_status'],x['wall_time'],x['peak_rss_kib'],x['swaps'],x['source_revision'],'; '.join(x['print_axioms'])])+'\n')
 for x in native:f.write('\t'.join(str(v) for v in [x['attempt'],' '.join(x['target']),x['exit_status'],x['wall_seconds'],x['peak_rss_kib'],x['swaps'],x['source_revision'],x['print_axioms']])+'\n')
print({k:s[k] for k in ['lean_charged','lean_remaining','lean_passes','lean_failures','kani_charged','next_unused_id','all_successful_axioms_standard']})
