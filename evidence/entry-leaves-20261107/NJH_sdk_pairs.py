from NJH_native import *
s=(E/'NJH_sdk.rs.txt').read_text()
for a,h in [('NJH_K005','shared_negative'),('NJH_K006','exclusive_contract'),('NJH_K007','exclusive_negative')]:
 r=fresh(a,'NJH_sdk::'+h,[('programs/r1-cost-probe/src/lib.rs','NJH_sdk',s)])
