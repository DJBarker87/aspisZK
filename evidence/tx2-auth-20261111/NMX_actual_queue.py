from NMX_formal import *
jobs=[('NMX_L193','NMX_BindCongruence')]
for offset,group in enumerate(reversed(range(6))):
 jobs += [(f'NMX_L{194+offset*2:03d}',f'NMX_Actual{group:02d}'),(f'NMX_L{195+offset*2:03d}',f'NMX_Match{group:02d}')]
jobs += [('NMX_L206','NMX_ActualRoot'),('NMX_L207','NMX_CutValueBridge')]
for a,m in jobs:
 r=run(a,'lean',m)
 if r['exit_status']:raise SystemExit(r['exit_status'])
