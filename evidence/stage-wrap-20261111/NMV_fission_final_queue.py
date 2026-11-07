from NMV_fission_native import *
import lzma
jobs=[
 ('stage2_pass',True),('stage2_clock',True),
 ('stage2_reply_control',False),('stage2_argument_control',False),('stage2_footprint_control',False),('stage2_clock_reply_control',False),
 ('stage1_child_error',True),('stage1_borrow_error',True),('stage1_copy',True),
 ('stage1_reply_control',False),('stage1_argument_control',False),('stage1_footprint_control',False),
 ('copy_pass',True),('copy_fail',False),('rejected_routes',True)]
for i,(name,positive) in enumerate(jobs,46):
 a=f'NMV_K{i:03}'
 if not (E/a/'receipt.json').exists():
  target=('NMV_' if name.startswith('copy_') else 'NMV_fission_')+name
  r=native(a,target)
 s=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode()
 assert 'VERIFICATION:- '+('SUCCESSFUL' if positive else 'FAILED') in s,(a,'no expected semantic verdict')
 assert 'unwinding assertion' not in s,(a,'unwinding failure')
