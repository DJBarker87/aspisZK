from NJH_native import *
s=(E/'NJH_lane.rs.txt').read_text()
for a,h in [('NJH_K008','iterator_cut'),('NJH_K009','iterator_cut_wrong')]:
 r=fresh(a,'r1_pool_adapter::NJH_lane::'+h,[('programs/r1-cost-probe/src/r1_pool_adapter.rs','NJH_lane',s)])
 if h=='iterator_cut' and r['exit_status']:break
