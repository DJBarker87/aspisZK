from NJH_formal import *
for a,m in [('NJH_L013','NJH_LaneIterator'),('NJH_L014','NJH_COMBINED_IMPORT')]:
 r=run(a,'lean',m)
 if r['exit_status']:break
