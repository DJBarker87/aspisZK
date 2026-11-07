from NMN_program import *
import lzma
items=[(29,'NMN_allocator_direct',True),(30,'NMN_allocator_omission',False),(31,'NMN_allocator_value_control',False),(32,'NMN_allocator_box_dispatch',False),(33,'NMN_allocator_from_raw',True),(34,'NMN_allocator_from_raw_control',False)]
for i,name,positive in items:
 a=f'NMN_K{i:03d}';r=program(a,'r1_pool_adapter::owned::NMN_program::'+name)
 s=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode()
 if positive:assert r['exit_status']==0,(a,s[-1000:])
 else:
  assert r['exit_status']!=0 and 'Failed Checks:' in s and 'CBMC timed out' not in s,(a,s[-1000:])
  if i!=32:assert 'unwinding assertion' not in s.split('Failed Checks:',1)[1].split('VERIFICATION:-',1)[0],a
