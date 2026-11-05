"""Mutation checks add closure checks; no solver/compiler replay."""
from pathlib import Path
import copy,json
from NHK_certificate import check
E=Path(__file__).resolve().parent;base=json.loads((E/'NHK_CLOSED.json').read_text());assert check(base)
cases=[('membership missing17',['membership','lengths'],[n for n in range(22) if n!=17]),('open membership',['membership','cases',11,'status'],'OPEN'),('unpaired membership',['membership','cases',11,'control'],'NHK_K018'),('wrong KMX',['native_environment','kmx_sha256'],'bad'),('drifted graph',['native_environment','graph_checked'],False),('changed lock',['native_environment','lock_unchanged'],False),('online build',['native_environment','offline'],False),('wrong features',['native_environment','core_features'],[]),('missing modifies',['native_contract','modifies'],[]),('independent poststate',['native_contract','same_poststate'],False),('distinct invocation',['schedule','same_invocation'],False),('post-word stop',['schedule','post_last_word_stop'],True),('wrong selected advance',['schedule','block_end_success_selects_next_advance'],False),('wrong fallback',['schedule','fallback_advance'],6),('missing eager pair',['schedule','eager_pairs'],7),('dropped failed call',['schedule','unsuccessful_call_kept'],False),('erased ideal suffix',['schedule','ideal_suffix_retained'],False),('success-only outcomes',['schedule','outcomes'],['sampler success']),('model-run producer',['producer'],'AspisR1.NGQ_Cuts.run'),('wrong export',['export'],'wrong'),('weakened payload domain',['domain','payload_max'],16384),('missing same cursor',['invariants'],['validState']),('cap raised',['limits','memory.max'],'17179869184'),('swap allowed',['limits','memory.swap.max'],'1024'),('legacy cohort',['cohort'],'legacy'),('wrong digest slot',['semantic_slots','digest'],32),('scan defects',['audit','dangling'],1),('nonstandard axiom',['audit','axioms'],['sorryAx']),('missing fixture',['audit','fixtures'],7),('cold release claim',['cold_release_replay'],True),('security claim',['security_target_established'],True),('trust removed',['trust','removed'],['P6']),('wrong source pin',['artifacts','NHK_CORRESPONDENCE.json'],'bad'),('wrong native positive',['native_contract','positive'],'NHK_K001'),('extraction budget',['budget_used','extraction'],1)]
results=[]
for name,path,value in cases:
 c=copy.deepcopy(base);d=c
 for k in path[:-1]:d=d[k]
 d[path[-1]]=value
 try:check(c)
 except (AssertionError,KeyError,ValueError):results.append(dict(mutation=name,rejected=True));continue
 raise AssertionError('mutation accepted: '+name)
(E/'NHK_MUTATIONS.json').write_text(json.dumps(dict(status='PASS',mutations=len(results),results=results),indent=2)+'\n');print(json.dumps(dict(status='PASS',rejected=len(results))))
