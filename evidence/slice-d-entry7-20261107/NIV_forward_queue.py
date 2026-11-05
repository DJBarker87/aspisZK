from NIV_native import *
s=''.join(l[1:] for l in (E/'NIV_forward.patch').read_text().splitlines(True) if l.startswith('+') and not l.startswith('+++'))
for i,name in enumerate(['entry3','entry3_wrong','entry7','entry7_wrong','process3','process3_wrong','process7','process7_wrong'],1):
 a='NIV_K%03d'%i
 if (E/a/'receipt.json').exists():continue
 r=fresh(a,'r1_pool_adapter::owned::NIV_forward::'+name,[('programs/r1-cost-probe/src/r1_pool_adapter_owned.rs','NIV_forward',s)])
 out=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode()
 expected=1 if name.endswith('_wrong') else 0
 if r['exit_status']!=expected or 'VERIFICATION' not in out or ('VERIFICATION:- FAILED' in out and expected==0):
  print('STOP_NATIVE_PACKET',a,flush=True);break
