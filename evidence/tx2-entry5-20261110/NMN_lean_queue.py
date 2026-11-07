from NMN_formal import *
for a,m in [('NMN_L013','NMN_241Prefix'),('NMN_L014','NMN_Inspect241')]:
 r=run(a,'lean',m)
 if r['exit_status']:break
