from NMX_formal import *
a=run('NMX_L312','lean','NMX_LengthGuard')
b=run('NMX_L313','lean','NMX_CanonicalCountFactor')
if a['exit_status']==0 and b['exit_status']==0:r=run('NMX_L314','lean','NMX_SevenSourceFold')
