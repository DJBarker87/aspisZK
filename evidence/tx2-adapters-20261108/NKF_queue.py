from NKF_wrappers import *
from NKF_formal import run
# One scope at a time, no unchanged timeout retry; stop at the first unexpected
# result so its shape can be inspected before dependent work continues.
def native(a,kind,field,mode):
 text=wrapper(kind,field)
 r=submit(a,'r1_pool_adapter::NKF_'+kind+'::wrapper_result',P,'NKF_'+kind,text,mode)
 if r['exit_status'] != (0 if mode=='positive' else 1):raise RuntimeError('Unexpected verdict '+a)
 return r
native('NKF_K005','master',0,'inverse')
for a,m in [('NKF_L005','NKF_MasterBox'),('NKF_L006','NKF_CheckpointBox'),('NKF_L007','NKF_BoxInstall')]:
 r=run(a,'lean',m)
 if r['exit_status']:raise RuntimeError('Lean source failure '+a)
for f in range(1,14):
 for j,mode in enumerate(['positive','inverse']):native('NKF_K'+str(6+2*(f-1)+j).zfill(3),'master',f,mode)
for f in range(6):
 for j,mode in enumerate(['positive','inverse']):native('NKF_K'+str(32+2*f+j).zfill(3),'checkpoint',f,mode)
