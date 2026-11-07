from NMV_fission_native import *
import lzma
jobs=[('slice2_pass',True),('slice2_reply_control',False),('slice2_argument_control',False),('slice2_footprint_control',False),('slice1_pass',True),('slice1_reply_control',False),('slice1_argument_control',False),('slice1_footprint_control',False),('clock_pass',True),('clock_reply_control',False),('copy_descriptor',True),('copy_pass',True),('copy_fail',False),('rejected_routes',True)]
for i,(name,positive) in enumerate(jobs,47):
 a=f'NMV_K{i:03}'
 if not (E/a/'receipt.json').exists():
  target=('NMV_' if name.startswith('copy_') and name!='copy_descriptor' else 'NMV_fission_')+name
  native(a,target)
 s=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode()
 assert 'VERIFICATION:- '+('SUCCESSFUL' if positive else 'FAILED') in s,(a,'no expected semantic verdict')
 assert 'unwinding assertion' not in s,(a,'unwinding failure')
