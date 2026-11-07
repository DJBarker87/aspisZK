from NMD_formal import *
from NMD_audit import audit
for a,m in [('NMD_L006','NMD_COMBINED_IMPORT'),('NMD_L007','NMD_ScanDriver')]:
 r=run(a,'lean',m);assert r['exit_status']==0
r=audit('NMD_L008','link','NMD_ScanDriver');assert r['exit_status']==0
for a,target in [('NMD_L009','fixtures'),('NMD_L010','scan'),('NMD_L011','batch0')]:
 r=audit(a,'audit',target)
 if r['exit_status']:
  print(json.dumps({'audit_nonzero_retained':a,'target':target,'raw_ax2_requires_inspection':True}),flush=True)
