from NJD_native import *
text=''.join(l[1:] for l in (E/'NJD_guards.patch').read_text().splitlines(True) if l.startswith('+') and not l.startswith('+++'))
for i,row in enumerate(json.loads((E/'NJD_GUARD_CUTS.json').read_text())):
 for j in range(2):
  n=row['name']+('_wrong' if j else '')
  rc=fresh('NJD_K'+str(2*i+j+2).zfill(3),'r1_pool_adapter::owned::NJD_stages::'+n,[('programs/r1-cost-probe/src/r1_pool_adapter_owned.rs','NJD_stages',text)])
  if rc['exit_status']!=(1 if j else 0):raise RuntimeError('unexpected guard verdict '+n)
