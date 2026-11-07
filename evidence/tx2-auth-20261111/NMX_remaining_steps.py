from NMX_formal import *
jobs=[('NMX_L127','NMX_S019')]+[(f'NMX_L{86+i-17:03d}',f'NMX_S{i:03d}') for i in range(20,56)]
for a,m in jobs:
 r=run(a,'lean',m)
 if r['exit_status']:raise SystemExit(r['exit_status'])
