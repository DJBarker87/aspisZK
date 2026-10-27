import ast,pathlib
from step import append
m='R1Z/PV_OptB_WorldFrames';ns='R1Z.PV_OptB_WorldFrames'
tree=ast.parse(pathlib.Path('evidence/pv-optb-20261027/offbad/world-steps.py').read_text())
steps=ast.literal_eval(next(n.iter for n in tree.body if isinstance(n,ast.For)))
for name,body in steps[1:]:append(m,ns,name,body)
