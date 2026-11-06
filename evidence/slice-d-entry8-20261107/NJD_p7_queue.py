from NJD_formal import *
for a,m in [('NJD_L011','NJD_LaneStep'),('NJD_L012','NJD_P7Inspect')]:
 r=run(a,'lean',m)
 if r['exit_status']:raise RuntimeError('repair '+m)
