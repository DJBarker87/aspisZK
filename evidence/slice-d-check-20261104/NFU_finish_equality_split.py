from pathlib import Path
import json
from NFU_add_inputs import update
E=Path(__file__).resolve().parent;P='crates/aspis-r1-cost-probe/src/NFU_verifier.rs';I=json.loads((E/'NFU_NATIVE_INPUTS.json').read_text());s=I[P]
for before,after in [('log.before==before',' && '.join(f'log.before[{i}]==before[{i}]'for i in range(9))),('final_state==after',' && '.join(f'final_state[{i}]==after[{i}]'for i in range(9)))]:
 assert before in s;s=s.replace(before,'('+after+')')
update({P:s},'NFU_finish_equality_split')
items=[];index=79
for g in list(range(3,8))+list(range(9,14)):
 for e in [0,1]:items.append(dict(attempt=f'NFU_K{index:03}',kind='kani',target=f'verifier::NFU_verifier::finish_g{g:02}',exit=e,env={'NFU_INVERT':'1'}if e else {}));index+=1
assert index==99
for i,t,e in [(99,'data_len_reply',0),(100,'data_len_reply',1),(51,'verifier_checkpoint_reply',0)]:items.append(dict(attempt=f'NFU_K{i:03}',kind='kani',target='r1_pool_adapter::owned::NFU_owned::'+t,exit=e,env={'NFU_PROGRAM':'1',**({'NFU_INVERT':'1'}if e else {})}))
(E/'NFU_QUEUE_FINAL.json').write_text(json.dumps(items,indent=1)+'\n')
