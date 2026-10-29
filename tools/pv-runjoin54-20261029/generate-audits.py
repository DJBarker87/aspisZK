from pathlib import Path
import json,re
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin54-20261029';L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
plan=json.loads((E/'build-plan.json').read_text());accepted={v['module']:v for p in E.glob('modules-*.json') for v in json.loads(p.read_text()) if v['accepted']}
def closure(m,seen=None):
 seen=set() if seen is None else seen
 if m in seen:return seen
 seen.add(m)
 for d in plan['modules'].get(m,{}).get('imports',[]):closure(d,seen)
 return seen
colliding={'R1Z.PV_AL_CircleOwnedTypes','AspisR72Sampler.Types'}
groups={'Neutral':[],'Model':[],'Source':[]}
for m in accepted:
 if 'Audit54' in m:continue
 if m.startswith(('R1Z.PV_RunJoin_Public','R1Z.PV_RunJoin_CircleParameter','R1Z.PV_RunJoin_CircleMapModel','R1Z.PV_RunJoin_CircleSampleModel','R1Z.PV_RunJoin_CircleR72MapAdapter')):k='Source'
 elif closure(m)&colliding:k='Model'
 else:k='Neutral'
 groups[k].append(m)
design={}
for kind,ms in groups.items():
 roots=[m for m in ms if not any(m!=n and m in closure(n) for n in ms)]
 names=[]
 for m in ms:
  p=R/plan['modules'][m]['path'];src=p.read_text()
  assert '#print axioms' in src,m
  names += [m+'.'+n for n in re.findall(r'^#print axioms (\S+)',src,re.M)]
 name='PV_RunJoin_'+kind+'Audit54'
 (L/(name+'.lean')).write_text('\n'.join('import '+r for r in sorted(roots))+'\n'+''.join('#print axioms '+n+'\n' for n in sorted(names)))
 design[kind]=dict(module='R1Z.'+name,roots=roots,modules=ms,names=names,colliding_types=sorted(set().union(*(closure(m) for m in roots))&colliding))
 assert 'R1Z.PV_AL_CircleOwnedTypes' not in design[kind]['colliding_types']
 if kind=='Neutral':assert not design[kind]['colliding_types']
(E/'audit-design.json').write_text(json.dumps(design,indent=2)+'\n')
print({k:dict(modules=len(v['modules']),roots=len(v['roots']),names=len(v['names'])) for k,v in design.items()})
