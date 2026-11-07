from NMX_formal import *
for a,m in [('NMX_L041','NMX_DirectValueFold'),('NMX_L042','NMX_WholeFrame')]:
 r=run(a,'lean',m)
 if r['exit_status']:raise SystemExit(r['exit_status'])
