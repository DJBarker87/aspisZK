from NJD_formal import *
for a,m in [('NJD_L008','NJD_EntrySpine'),('NJD_L009','NJD_LaneStep')]:
 r=run(a,'lean',m)
 if r['exit_status']:raise RuntimeError('repair '+m)
