from NMX_formal import *
for a,m in [('NMX_L036','NMX_FrameLaws'),('NMX_L037','NMX_Inspect'),('NMX_L038','NMX_ErasureLaws')]:
 r=run(a,'lean',m)
 if r['exit_status']:raise SystemExit(r['exit_status'])
