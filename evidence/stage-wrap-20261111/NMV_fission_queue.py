from NMV_fission_native import *
import lzma
jobs=[('NMV_K036','stage2_reply_control',False),('NMV_K037','stage2_argument_control',False),('NMV_K038','stage2_footprint_control',False),('NMV_K039','stage1_child_error',True),('NMV_K040','stage1_borrow_error',True),('NMV_K041','stage1_copy',True),('NMV_K042','stage1_reply_control',False),('NMV_K043','stage1_argument_control',False),('NMV_K044','stage1_footprint_control',False)]
for a,name,positive in jobs:
 if not (E/a/'receipt.json').exists():r=native(a,'NMV_fission_'+name)
 s=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode()
 assert 'VERIFICATION:- '+('SUCCESSFUL' if positive else 'FAILED') in s,(a,'no expected semantic verdict')
 assert 'unwinding assertion' not in s,(a,'unwinding failure')
