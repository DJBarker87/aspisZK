from pathlib import Path
E=Path(__file__).resolve().parent;p=E/'NBU_more.rs.txt';s=p.read_text();attrs=s[s.index('#[kani::proof]'):s.index('fn NBU_validator_control')].replace('1881','34')
checks='''assert_eq!(pool[k],public.pool[k]);assert_eq!(deployment[k],public.deployment_domain[k]);assert_eq!(sequence,public.anchor_sequence);assert_eq!(anchor[d],public.anchor_root[d]);assert_eq!(nullifier[d],public.nullifier[d]);assert_eq!(asset,public.asset_id);'''
body='''let s=NBU_statement();let k:usize=kani::any();kani::assume(k<32);let d:usize=kani::any();kani::assume(d<8);let (pool,deployment,sequence,anchor,nullifier,asset)=statement_public_common(&s);match &s{PoolV1PairForestTerminalStatementV1::PrivateTransfer{public,..}=>{'''+checks+'''},PoolV1PairForestTerminalStatementV1::Withdrawal{public,..}=>{'''+checks+'}}'
for neg in ['', '_negative']:
 b=body.replace('assert_eq!(pool[k],public.pool[k])','assert_ne!(pool[k],public.pool[k])') if neg else body
 s+='\n'+attrs+'fn NBU_parts'+neg+'(){'+b+'}\n'
p.write_text(s)
