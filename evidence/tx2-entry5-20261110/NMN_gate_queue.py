from NMN_audit import *
for a,kind,target in [('NMN_L015','lean','NMN_COMBINED_IMPORT'),('NMN_L016','lean','NMN_ScanDriver'),('NMN_L017','link','NMN_ScanDriver'),('NMN_L018','audit','fixtures'),('NMN_L019','audit','batch0'),('NMN_L020','audit','batch1'),('NMN_L021','audit','scan')]:
 r=run(a,kind,target) if kind=='lean' else audit(a,kind,target)
 if r['exit_status']:break
