from pathlib import Path
import re,subprocess,json
E=Path(__file__).resolve().parent;R=E.parents[1];O=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
base=(E/'base.txt').read_text().strip()
new=subprocess.check_output(['git','diff','--name-only',base,'--',str(O)],cwd=R,text=True).splitlines()
new+=subprocess.check_output(['git','ls-files','--others','--exclude-standard','--',str(O)],cwd=R,text=True).splitlines()
paths=[R/p for p in sorted(set(new)) if p.endswith('.lean') and '/PV_Inv_AuditInv3' not in p]
groups=[[],[],[]]
for p in paths:
 n=p.stem
 if re.fullmatch('PV_Inv_MaskTail[0-9]+',n):groups[0].append(p)
 elif n.startswith('PV_Inv_Guard'):groups[2].append(p)
 else:groups[1].append(p)
for i,(name,ps) in enumerate(zip(['Masks','Bindings','Coupling'],groups)):
 s=''
 if i==2:s+='import R1Z.PV_Inv_AuditInv3Masks\nimport R1Z.PV_Inv_AuditInv3Bindings\nimport R1Z.PV_Inv_CouplingPole\nimport R1Z.PV_Inv_HeadlineCharge\nimport R1Z.PV_Inv_GuardedRegistry\n'
 for p in ps:s+='import R1Z.'+p.stem+'\n'
 s+='set_option autoImplicit false\n'
 for p in ps:
  for decl in re.findall(r'^theorem (\w+)',p.read_text(),re.M):s+=f'#print axioms R1Z.{p.stem}.{decl}\n'
 if i==2:s+='#print axioms R1Z.PV_Inv_CouplingPole.contained\n#print axioms R1Z.PV_Inv_HeadlineCharge.mass_at_existing_term\n#print axioms R1Z.PV_Inv_HeadlineCharge.numerical_term\n#print axioms R1Z.PV_Inv_GuardedRegistry.no_zero\n'
 (O/('PV_Inv_AuditInv3'+name+'.lean')).write_text(s)
 print(name,len(ps),s.count('#print axioms'))
(E/'audit-targets.json').write_text(json.dumps(['R1Z/PV_Inv_AuditInv3'+n for n in ['Masks','Bindings','Coupling']],indent=2)+'\n')
