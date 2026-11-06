from NLA_tail_native import attempt
from NLA_registry import attempt as registry
from NLA_formal import run
n=53
for part in ['length','absolute','iteration','boxmove','boxunique','boxframe','status','pdaoutput']:
 for mode in ['positive','inverse']:
  r=attempt(f'NLA_K{n:03}',part,mode);n+=1
  assert r['exit_status']==(0 if mode=='positive' else 1)
for mode in ['positive','inverse']:
 r=registry(f'NLA_K{n:03}','readonly_data',mode);n+=1
 assert r['exit_status']==(0 if mode=='positive' else 1)
