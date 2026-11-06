from NJD_native import *
s=''.join(l[1:] for l in (E/'NJD_lane.patch').read_text().splitlines(True) if l.startswith('+') and not l.startswith('+++'))
for a,n,expected in [('NJD_K018','frontier_decode_cut',0),('NJD_K019','frontier_decode_cut_wrong',1)]:
 rc=fresh(a,'r1_pool_adapter::NJD_lane::'+n,[('programs/r1-cost-probe/src/r1_pool_adapter.rs','NJD_lane',s)])
 if rc['exit_status']!=expected:raise RuntimeError('unexpected lane verdict')
