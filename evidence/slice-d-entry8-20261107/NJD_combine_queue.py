from NJD_formal import *
for a,m in [('NJD_L020','NJD_LaneStep'),('NJD_L021','NJD_GuardCuts'),('NJD_L022','NJD_COMBINED_IMPORT')]:
 r=run(a,'lean',m)
 if r['exit_status']:raise RuntimeError('repair '+m)
