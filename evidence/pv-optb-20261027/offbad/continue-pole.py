import ast,pathlib,subprocess
s=ast.parse(pathlib.Path('evidence/pv-optb-20261027/offbad/pole-steps.py').read_text())
steps=ast.literal_eval(next(n.value for n in s.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='steps' for t in n.targets)))
p=pathlib.Path('docs/research/v8-r0-zk-20261009/lean/R1Z/PV_OptB_OffPole.lean');ns='R1Z.PV_OptB_OffPole'
for a,(name,body) in enumerate(steps[6:],44622):
 p.write_text(p.read_text().replace('end '+ns,body+'\n#print axioms '+name+'\nend '+ns))
 r=subprocess.run(['python3','evidence/pv-optb-20261027/offbad/check.py',str(a),'R1Z/PV_OptB_OffPole'],capture_output=True,text=True)
 print(a,name,r.returncode,r.stdout[-1700:] if r.returncode else 'checked',flush=True)
 if r.returncode:break
