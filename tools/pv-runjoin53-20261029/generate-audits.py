from pathlib import Path
import json,re
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin53-20261029';L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
accepted={v['module']:v for p in E.glob('modules-*.json') for v in json.loads(p.read_text()) if v['accepted'] and 'Audit53' not in v['module']}
groups={'Neutral':[m for m in accepted if m not in ['R1Z.PV_RunJoin_CircleInstalled52','R1Z.PV_RunJoin_CircleOwnedTower52']], 'Model':['R1Z.PV_RunJoin_CircleInstalled52'],'Owned':['R1Z.PV_RunJoin_CircleOwnedTower52']}
out={}
for kind,mods in groups.items():
 names=[]
 for m in mods:
  for s in accepted[m]['axioms']:
   z=re.match(r"'([^']+)'",s)
   if z:names.append(z[1])
 stem='PV_RunJoin_'+kind+'Audit53';p=L/(stem+'.lean')
 p.write_text('\n'.join('import '+m for m in sorted(mods))+'\nset_option autoImplicit false\n'+''.join('#print axioms '+n+'\n' for n in sorted(set(names))))
 out[kind]={'module':'R1Z.'+stem,'imports':sorted(mods),'names':sorted(set(names))}
(E/'audit-design.json').write_text(json.dumps(out,indent=2)+'\n')
print({k:(len(v['imports']),len(v['names'])) for k,v in out.items()})
