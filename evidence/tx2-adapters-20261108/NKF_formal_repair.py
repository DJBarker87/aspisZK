from NKF_formal import *
for a,m in [('NKF_L009','NKF_ArrayFrame'),('NKF_L010','NKF_BoxFields'),('NKF_L011','NKF_Roots'),('NKF_L012','NKF_LaneTrace'),('NKF_L013','NKF_PdaModel')]:
 r=run(a,'lean',m)
 if r['exit_status']:raise RuntimeError('Focused formal failure '+a)
