#!/usr/bin/env python3
"""Audit actual-View frame discharge and selected/literal query transport."""
from pathlib import Path
import hashlib,json,re
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013'
E=B/'evidence/s126-current-caller-20261021';S=B/'lean-candidates/s126-caller-boundary-20261021'
load=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=load(E/'s1-selected-query-targets.json');a=load(E/'accepted-targets.json')['targets'];pins=load(E/'s1-selected-query-import-pins.json');wall=0.;rss=0;reports=0
for target,attempt in m['targets'].items():
 p=S/(target+'.lean');r=load(E/attempt/'receipt.json')
 assert r['exit_status']==0 and r['swaps']==0 and r['print_axioms'],target
 assert a[target]['receipt']==attempt+'/receipt.json'
 assert sha(p)==sha(E/attempt/'source.lean')==r['source_sha256']==pins['targets'][target]['source_sha256']
 assert r['object_sha256']==pins['targets'][target]['object_sha256']
 assert '-j1' in r['command'] and '-M4400' in r['command']
 assert not re.search(r'\b(sorry|native_decide|bv_decide)\b|^\s*(axiom|opaque)\b|set_option\s+(maxHeartbeats|maxRecDepth)',p.read_text(),re.M)
 for x in r['print_axioms']:
  if 'does not depend on any axioms' not in x:
   ax=re.search(r'depends on axioms:\s*\[([^]]*)\]',x,re.S)
   assert ax and set(re.findall(r'[A-Za-z_.]+',ax[1]))<={'propext','Classical.choice','Quot.sound'},(target,x)
  reports+=1
 wall+=r['wall_seconds'];rss=max(rss,r['peak_rss_bytes'])
 for f in (E/attempt).rglob('*'):
  if f.is_file():assert f.suffix not in ['.olean','.llbc','.rlib','.rmeta','.o','.a','.so','.dylib']
for kind,key in [('tool','scripts'),('source','sources'),('reused','packets')]:
 for path,h in load(E/f's1-selected-query-{kind}-pins.json')[key].items():assert sha(R/path)==h,path
frame=(S/'S1WideViewFinalLengthV1.lean').read_text()
assert 'wide_view_final_frame proof semantic y1 out accepted' in frame and 'final_width_total' in frame
payload=(S/'S1SelectedQueryPayloadV1.lean').read_text()
assert 'source_length_cast' in payload and 'queryAbsorb_bytes' in payload and 'fixedQuery31_selected' in payload
assert 'SamplerSuffixSourceFrames.opening_absorb_frame' in payload
literal=(S/'S1LiteralQueryProgramV1.lean').read_text()
assert 'LiteralByteSampler.samp 31 P' in literal and 'LiteralTranscript.erasePrefix P' in literal
execution=(S/'S1LiteralQueryExecutionV1.lean').read_text()
assert '(stateEq :' in execution and 'literal_query_p3_accepted' in execution
parent=(S/'S1OwnedStage1SelectedQueryV1.lean').read_text()
assert 'wide_view_final_length proof semantic y1 v hview' in parent
assert 'owned_stage1_closed_query_program_p3 adapterOps ops sha' in parent
assert 'Row31SelectedProgramMeaning sha' in parent and 'v.final_message.length=2048' in parent
for premise in ['(hquery :','(hframe :','(hlen :','(stateEq :']:
 assert premise not in parent
assert m['actual_owned_view_frame_discharge'] and m['selected_query_constructor_equal'] and m['literal_row31_program_equation']
assert not m['actual_full_prefix_state_join'] and not m['native_sdk_binding'] and not m['whole_s1_closed'] and not m['whole_s6_closed']
print(json.dumps(dict(targets=len(m['targets']),wall_seconds=wall,peak_rss_bytes=rss,swaps=0,standard_or_empty_axiom_reports=reports,actual_owned_view_frame_discharge=True,selected_query_constructor_equal=True,literal_row31_program_equation=True,actual_full_prefix_state_join=False,whole_s1_closed=False)))
