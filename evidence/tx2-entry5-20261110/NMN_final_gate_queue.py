from NMN_audit import *
for a,kind,target in [('NMN_L024','lean','NMN_COMBINED_IMPORT'),('NMN_L025','audit','batch2'),('NMN_L026','audit','scan')]:
 r=run(a,kind,target) if kind=='lean' else audit(a,kind,target)
 if r['exit_status']:break
