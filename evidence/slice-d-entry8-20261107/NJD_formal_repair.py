from NJD_formal import *
for a,m in [('NJD_L005','NJD_GuardCuts'),('NJD_L006','NJD_EntrySpine')]:
 r=run(a,'lean',m)
 if r['exit_status']:raise RuntimeError('repair '+m)
