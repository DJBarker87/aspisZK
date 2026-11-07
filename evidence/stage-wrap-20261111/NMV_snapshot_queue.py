from NMV_program import *
for i,target in [(14,'NMV_snapshot_footprint_control'),(15,'NMV_copy_pass'),(16,'NMV_copy_fail')]:
 r=program(f'NMV_K{i:03}',target)
 raw=lzma.decompress((E/f'NMV_K{i:03}'/'stdout.log.xz').read_bytes()).decode()
 if 'VERIFICATION:-' not in raw or 'unwinding assertion' in raw:break
 if i==15 and r['exit_status']!=0:break
