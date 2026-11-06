from NJD_formal import *
for a,m in [('NJD_L014','NJD_DigestLaw'),('NJD_L015','NJD_P7Inspect')]:
 r=run(a,'lean',m)
 # Independent inspections never hold an unrelated proof behind a failure.
