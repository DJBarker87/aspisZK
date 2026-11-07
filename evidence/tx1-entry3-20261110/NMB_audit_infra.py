from NMB_audit import *
for a,target in [('NMB_L079','NMB_ProofDriver'),('NMB_L080','NMB_ScanDriver')]:
 r=link(a,target)
 if r['exit_status']:raise RuntimeError('link failed '+a)
for a,mode in [('NMB_L081','fixtures'),('NMB_L082','scan')]:audit(a,mode)
