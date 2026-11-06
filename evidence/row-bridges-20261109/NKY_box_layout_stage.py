from NKY_box_native import *
for n,(kind,mode) in enumerate([(k,m)for k in ['checkpoint','master']for m in ['positive','value','allocation']],8):
 a=f'NKY_K{n:03}'
 r=run(a,kind,mode)
 log=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode()
 if mode=='positive':assert r['exit_status']==0 and 'VERIFICATION:- SUCCESSFUL'in log
 else:assert r['exit_status']!=0 and 'VERIFICATION:- FAILED'in log and 'timed out'not in log
 print(a,'layout and ownership expected verdict recorded',flush=True)
