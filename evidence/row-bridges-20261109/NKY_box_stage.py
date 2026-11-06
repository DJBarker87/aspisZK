from NKY_box_native import *
for a,kind,mode in [('NKY_K003','checkpoint','value'),('NKY_K004','checkpoint','allocation'),('NKY_K005','master','positive'),('NKY_K006','master','value'),('NKY_K007','master','allocation')]:
 r=run(a,kind,mode)
 log=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode()
 if mode=='positive':assert r['exit_status']==0 and 'VERIFICATION:- SUCCESSFUL'in log
 else:assert r['exit_status']!=0 and 'VERIFICATION:- FAILED'in log and 'timed out'not in log
 print(a,kind,mode,'expected verdict recorded',flush=True)
