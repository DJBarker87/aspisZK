from NMX_formal import *
jobs=[('NMX_L083','NMX_RSL233Fold'),('NMX_L084','NMX_CanonicalCuts'),('NMX_L085','NMX_Observation')]
jobs += [(f'NMX_L{86+i-17:03d}',f'NMX_S{i:03d}') for i in range(17,56)]
for a,m in jobs:
 r=run(a,'lean',m)
 if r['exit_status']:raise SystemExit(r['exit_status'])
