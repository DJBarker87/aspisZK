from pathlib import Path
import json
H=Path(__file__).resolve().parent;x=json.loads((H/'charon-001.json').read_text());old=x['command'];cmd=[];i=0
while i<len(old):
 if old[i]=='--start-from' and '{OwnedAccount}' in old[i+1]: i+=2;continue
 cmd.append(old[i].replace('{OwnedAccount}','_'));i+=1
idx=cmd.index('--dest-file')
extra=[]
for n in ['aspis_statement::pool_v1::format::PoolIdentityV1','aspis_statement::pool_v1::format::VerifierPolicyV1','aspis_statement::pool_v1::pair_forest_terminal::PoolV1PairForestTerminalRequestV1','aspis_statement::pool_v1::pair_forest_terminal::PoolV1PairForestTerminalPaymentV1']:
 extra+=['--include',n]
extra+=['--start-from','crate::first_decoded','--include','crate::first_decoded']
cmd[idx:idx]=extra
x.update(attempt='charon-002',command=cmd,change='Do not root nested impl patterns: root only callers; include reachable methods via wildcard. Add concrete identity/request layouts and first_decoded wrapper.')
(H/'charon-002.json').write_text(json.dumps(x,indent=2)+'\n')
