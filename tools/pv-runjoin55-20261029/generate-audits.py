from pathlib import Path
import json,re
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin55-20261029';L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
plan=json.loads((E/'build-plan.json').read_text());accepted={v['module']:v for p in sorted(E.glob('modules-*.json')) for v in json.loads(p.read_text()) if v['accepted'] and v['module']!='R1Z.PV_RunJoin_BackendStore55'}
def closure(m,seen=None):
 seen=set() if seen is None else seen
 if m in seen:return seen
 seen.add(m)
 for d in plan['modules'].get(m,{}).get('imports',[]):closure(d,seen)
 return seen
groups={'Circle':[],'Backend':[],'Native':[]}
for m in accepted:
 if 'Audit55' in m:continue
 groups['Circle' if 'Circle' in m else 'Backend' if 'Backend' in m else 'Native'].append(m)
design={}
for kind,mods in groups.items():
 roots=[m for m in mods if not any(m!=n and m in closure(n) for n in mods)]
 names=[]
 for m in mods:
  src=(R/plan['modules'][m]['path']).read_text()
  names += [m+'.'+n for n in re.findall(r'^#print axioms (\S+)',src,re.M)]
 name='PV_RunJoin_'+kind+'Audit55'
 (L/(name+'.lean')).write_text('\n'.join('import '+r for r in sorted(roots))+'\n'+''.join('#print axioms '+n+'\n' for n in sorted(set(names))))
 design[kind]=dict(module='R1Z.'+name,roots=roots,modules=mods,names=sorted(set(names)))
 assert 'R1Z.PV_RunJoin_BackendStore55' not in set().union(*(closure(m) for m in roots))
(E/'audit-design.json').write_text(json.dumps(design,indent=2)+'\n')
print({k:dict(modules=len(v['modules']),roots=len(v['roots']),names=len(v['names'])) for k,v in design.items()})
