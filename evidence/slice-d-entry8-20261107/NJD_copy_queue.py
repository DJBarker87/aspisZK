from NJD_native import *
s=''.join(l[1:] for l in (E/'NJD_lane.patch').read_text().splitlines(True) if l.startswith('+') and not l.startswith('+++'))
for i,n in enumerate(['KMX_slice_correct','KMX_slice_wrong','KMX_ptr_correct','KMX_ptr_wrong']):
 rc=fresh('NJD_K'+str(21+i).zfill(3),'r1_pool_adapter::NJD_lane::KMX_checks::'+n,[('programs/r1-cost-probe/src/r1_pool_adapter.rs','NJD_lane',s)])
 if rc['exit_status']!=i%2:raise RuntimeError('copy calibration unexpected')
