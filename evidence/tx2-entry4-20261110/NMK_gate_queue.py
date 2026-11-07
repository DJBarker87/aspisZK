from NMK_audit import *
r=run('NMK_L010','lean','NMK_COMBINED_IMPORT');assert r['exit_status']==0
r=run('NMK_L011','lean','NMK_ScanDriver');assert r['exit_status']==0
r=audit('NMK_L012','link','NMK_ScanDriver');assert r['exit_status']==0
for a,mode in [('NMK_L013','fixtures'),('NMK_L014','batch0'),('NMK_L015','batch1'),('NMK_L016','scan')]:
 r=audit(a,'audit',mode);assert r['exit_status']==0,(a,mode)
