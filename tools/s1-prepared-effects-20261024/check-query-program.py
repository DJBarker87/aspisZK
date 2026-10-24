#!/usr/bin/env python3
"""Audit concrete query program/event transport and its SAME caller/P3 join."""
from pathlib import Path
import hashlib,json,re
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013'
E=B/'evidence/s126-current-caller-20261021';S=B/'lean-candidates/s126-caller-boundary-20261021'
load=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=load(E/'s1-query-program-targets.json');a=load(E/'accepted-targets.json')['targets'];pins=load(E/'s1-query-program-import-pins.json');wall=0.;rss=0;reports=0
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
 for path,h in load(E/f's1-query-program-{kind}-pins.json')[key].items():assert sha(R/path)==h,path
relation=(S/'S1QueryProgramRelationV1.lean').read_text()
assert '∀ reply,SameReads R (f reply) (g reply)' in relation
assert 'SameReads.independentMean_le' in relation and 'SameReads.lazyMean_le' in relation
concrete=(S/'S1QueryClosedRelationV1.lean').read_text()
assert 'closed_query31_same_reads' in concrete and 'apply source_leaf_related' in concrete
for premise in ['(oracleLaw :','(scannerLaw :','(terminal :']:
 assert premise not in concrete
event=(S/'S1QueryEventTransportV1.lean').read_text()
assert 'Table Bytes State' in event and 'closed_query31_memoized_event_le' in event
assert 'closed_query31_independent_event_le' in event and 'abbrev QueryEvent := List (Bytes × State)' in event
p3=(S/'S1QueryP3ExecutionV1.lean').read_text();assert 'closed_query_p3_execution' in p3 and 'queries_run_value' in p3
parent=(S/'S1OwnedStage1QueryProgramP3V1.lean').read_text()
assert 'current_owned_stage1_closed_claim_rank_and_query_program (installP3Adapter adapterOps sha)' in parent
assert 'row31P3_from_program_meaning' in parent and 'Row31P3ProgramMeaning sha' in parent
assert '(hquery :' not in parent and '(hfirst :' not in parent and '(hashLaw :' not in parent
assert m['same_owned_parent'] and m['all_reply_structural_relation'] and m['independent_and_memoized_event_transport'] and m['p3_actual_query_execution']
assert not m['native_iterator_binding'] and not m['native_sdk_binding'] and not m['selected_literal_row31_instance'] and not m['whole_s1_closed'] and not m['whole_s6_closed']
print(json.dumps(dict(targets=len(m['targets']),wall_seconds=wall,peak_rss_bytes=rss,swaps=0,standard_or_empty_axiom_reports=reports,all_reply_structural_relation=True,independent_and_memoized_event_transport=True,p3_actual_query_execution=True,same_owned_parent=True,whole_s1_closed=False)))
