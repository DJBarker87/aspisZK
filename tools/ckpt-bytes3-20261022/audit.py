#!/usr/bin/env python3
"""Audit the focused packet without rerunning a proof or build."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2]
E=R/'docs/research/100bit-spend-path-20261013/evidence/ckpt-bytes3-20261022'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
subprocess.run(['python3','-B',str(R/'tools/ckpt-bytes3-20261022/source_check.py')],check=True)
m=json.loads((E/'manifest.json').read_text()); finals=[a for a in m['attempts'] if a['final_current']]
assert len(finals)==10,len(finals)
for a in finals:
 assert a['exit']==0 and a['swaps']==0 and a['axioms_accepted'] and a['source_unchanged']
 source=R/'docs/research/100bit-spend-path-20261013/lean'/(a['module']+'.lean')
 assert sha(source)==a['source_sha256']
 assert a['axioms']
 for line in a['axioms']:
  assert not any(x in line for x in ['sorryAx','_native','Lean.ofReduceBool'])
# Compare exactly the covered harness and helper bodies when unrelated harness
# changes occurred after an independent proof (no unchanged rerun is needed).
def fun(s,name):
 a=s.index('fn '+name+'(');b=s.index('{',a);i=b+1;d=1
 while d:d+=(s[i]=='{')-(s[i]=='}');i+=1
 return s[a:i]
current=(R/'tools/ckpt-bytes3-20261022/src/lib.rs').read_text()
accepted={'semantic-1':['semantic_section','words','limbs'],
 'weights-2':['weight_section','words','limbs','any_k'],
 'filled-2':['filled_content','any_k'],'resize-2':['resize_content','any_k'],
 'box-2':['box_prepared_content','any_e','any_k']}
rows=[]
for attempt,names in accepted.items():
 p=E/'kani'/attempt;a=json.loads((p/'receipt.json').read_text())
 assert a['exit_status']==0 and a['swaps']==0 and a['cgroup_swap_peak_bytes']==0
 assert a['limits']=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0','pids.max':'64'}
 assert a['environment']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
 assert 'VERIFICATION SUCCESSFUL' in (p/'stdout.log').read_text()
 snapshot=(p/'source.rs.txt').read_text()
 for n in names:assert fun(snapshot,n)==fun(current,n),(attempt,n)
 for name,digest in a['source_sha256'].items():
  if name.startswith('crates/') or name.endswith(('reader-source.rs','sections-source.rs')):
   assert sha(R/name)==digest,(attempt,name)
 reservation=json.loads((E/'kani'/('reservation-'+attempt+'.json')).read_text())
 assert reservation['allowed'] and reservation['all_populated_scopes_bounded']
 rows.append({'attempt':attempt,'exit':0,'covered_functions':names,'wall_seconds':a['wall_seconds'],
  'peak_rss_kib':a['peak_rss_kib'],'print_axioms':a['print_axioms']})
for p in E.rglob('*.json'):assert p.stat().st_size<=5_000_000,p
source=(R/'docs/research/100bit-spend-path-20261013/lean/CheckpointBytes3Freeze.lean').read_text()
assert len(re.findall(r'^#print axioms ',source,re.M))==35
result={'schema':'ckpt-bytes3-focused-audit-v1','lean_final_modules':len(finals),
 'axiom_reports_in_freeze':35,'lean_final_peak_rss_bytes':max(a['peak_rss_bytes'] for a in finals),
 'lean_final_swaps':0,'accepted_kani':rows,'decoder_identification_closed':True,
 'concrete_resume_ops_source_instance_closed':False,'source_stage_join_closed':False,
 'elf_rebuild_trigger':False,'coherent_frozen_release_replay':False,
 'allocation_gates':'successful-content only; Kani native allocator uses --no-malloc-may-fail',
 'next_consumer':'Concrete AspisR1Stage2.ResumeOps; successful_fields; reached_stage/strictStage; decision_observation/dV_frozen2'}
(E/'audit-result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
