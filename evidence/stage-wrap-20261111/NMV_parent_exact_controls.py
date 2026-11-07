from NMV_fission_native import *
import lzma
for a,target,base in [('NMV_K063','NMV_fission_stage2_parent_argument_control','NMV_K035'),('NMV_K064','NMV_fission_stage1_parent_argument_control','NMV_K041')]:
 r=native(a,target,parent=True,parent_base=base)
 s=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode()
 assert 'VERIFICATION:- FAILED' in s
 assert 'unwinding assertion' not in s
