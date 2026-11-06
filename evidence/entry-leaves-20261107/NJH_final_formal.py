from NJH_formal import *
for a,m in [('NJH_L018','NJH_ReplyComposition'),('NJH_L019','NJH_COMBINED_IMPORT')]:
 r=run(a,'lean',m)
 if r['exit_status']:raise RuntimeError('Repair '+m)
