from NMX_formal import *
jobs=[('NMX_L158','NMX_CallArguments'),('NMX_L147','NMX_FoldedProgram'),('NMX_L148','NMX_Question')]
for a,m in jobs:
 r=run(a,'lean',m)
 if r['exit_status']:raise SystemExit(r['exit_status'])
