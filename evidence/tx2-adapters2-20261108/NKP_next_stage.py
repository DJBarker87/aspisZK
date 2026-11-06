from NKP_box_stage import attempt
from NKP_formal import run
for a,kind,mode in [('NKP_K042','checkpoint','positive'),('NKP_K043','checkpoint','inverse'),('NKP_K044','master','positive'),('NKP_K045','master','inverse')]:attempt(a,kind,-1,mode)
rc=run('NKP_L001','lean','NKP_BoxCuts');assert rc['exit_status']==0
