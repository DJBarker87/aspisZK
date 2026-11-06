from NJD_formal import *
for a,m in [('NJD_L013','NJD_P7Inspect'),('NJD_L014','NJD_DigestLaw')]:
 r=run(a,'lean',m)
 if r['exit_status']:raise RuntimeError('repair '+m)
