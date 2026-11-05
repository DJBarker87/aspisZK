from NIS_native import *
s=''.join(l[1:] for l in (E/'NIS_forward.patch').read_text().splitlines(True) if l.startswith('+') and not l.startswith('+++'))
for i,name in enumerate(['entry3','entry3_wrong','entry7','entry7_wrong','process3','process3_wrong','process7','process7_wrong'],50):
 r=fresh('NIS_K%03d'%i,'r1_pool_adapter::owned::NIS_forward::'+name,[('programs/r1-cost-probe/src/r1_pool_adapter_owned.rs','NIS_forward',s)])
 if r['exit_status'] not in [0,1]:break
