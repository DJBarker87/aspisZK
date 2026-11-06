from NJH_native import *
s=(E/'NJH_lane.rs.txt').read_text()
for a,h in [('NJH_K010','KMX_slice_correct'),('NJH_K011','KMX_slice_wrong'),('NJH_K012','KMX_ptr_correct'),('NJH_K013','KMX_ptr_wrong')]:
 r=fresh(a,'r1_pool_adapter::NJH_lane::KMX_checks::'+h,[('programs/r1-cost-probe/src/r1_pool_adapter.rs','NJH_lane',s)])
