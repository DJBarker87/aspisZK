from NIV_native import *
s=''.join(l[1:] for l in (E/'NIV_owned.patch').read_text().splitlines(True) if l.startswith('+') and not l.startswith('+++'))
for j in range(14):
 a='NIV_K%03d'%(j+24);name='guard_'+str(7+j//2)+('_wrong' if j%2 else '')
 if (E/a/'receipt.json').exists():continue
 r=fresh(a,'r1_pool_adapter::owned::NIV_owned::'+name,[('programs/r1-cost-probe/src/r1_pool_adapter_owned.rs','NIV_owned',s)])
 out=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode()
 if r['exit_status']!=j%2 or ('VERIFICATION:- FAILED' if j%2 else 'VERIFICATION:- SUCCESSFUL') not in out:
  print('STOP_NATIVE_PACKET',a,flush=True);break
