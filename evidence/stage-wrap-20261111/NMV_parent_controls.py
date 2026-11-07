from NMV_fission_native import *
import lzma
for a,target in [('NMV_K061','NMV_fission_stage2_parent_argument_control'),('NMV_K062','NMV_fission_stage1_parent_argument_control')]:
 r=native(a,target,parent=True)
 s=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode()
 assert 'VERIFICATION:- FAILED' in s,(a,'no expected negative verdict')
 assert 'unwinding assertion' not in s,(a,'unwinding failure')
