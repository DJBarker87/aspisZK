from NKF_formal import *
import time
while not (E/'NKF_K043/receipt.json').exists():time.sleep(0.5)
for a,m in [('NKF_L008','NKF_ArrayFrame'),('NKF_L009','NKF_BoxFields'),('NKF_L010','NKF_Roots'),('NKF_L011','NKF_LaneTrace'),('NKF_L012','NKF_PdaModel')]:
 r=run(a,'lean',m)
 if r['exit_status']:raise RuntimeError('Focused formal failure '+a)
