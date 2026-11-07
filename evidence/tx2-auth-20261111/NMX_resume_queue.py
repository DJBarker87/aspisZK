from NMX_formal import *
for i,m in enumerate(['NMX_RSL_Base','NMX_RSL_Pool','NMX_RSL_TX2_217','NMX_RSL_TX2_234','NMX_RSL_TX2_233'],53):
 r=run(f'NMX_L{i:03d}','lean',m)
 if r['exit_status']:raise SystemExit(r['exit_status'])
