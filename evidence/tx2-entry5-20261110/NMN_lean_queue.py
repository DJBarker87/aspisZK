from NMN_formal import *
for a,m in [('NMN_L006','NMN_Observer'),('NMN_L007','NMN_CallerDomain'),('NMN_L008','NMN_Headline')]:
 r=run(a,'lean',m)
 if r['exit_status']:break
