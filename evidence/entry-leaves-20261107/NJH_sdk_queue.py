from NJH_native import *
s=(E/'NJH_sdk.rs.txt').read_text()
r=fresh('NJH_K001','NJH_sdk::shared_contract',[('programs/r1-cost-probe/src/lib.rs','NJH_sdk',s)])
