from pathlib import Path
import re,json,hashlib,subprocess
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z';E=R/'evidence/pv-runjoin52-20261029';p=json.loads((E/'build-plan.json').read_text());accepted={v['module']:v for f in E.glob('modules-*.json') for v in json.loads(f.read_text()) if v['accepted']}
# Discard only unaccepted plan pins, never objects or authoritative sources.
for m in list(p['modules']):
 if m.endswith('52') and m not in accepted: del p['modules'][m]
(E/'build-plan.json').write_text(json.dumps(p,indent=2)+'\n')
def closure(m):
 seen=set()
 def walk(n):
  if n in seen:return
  seen.add(n)
  for d in p['modules'].get(n,{}).get('imports',[]):walk(d)
 walk(m);return seen
owned='R1Z.PV_AL_CircleOwnedTypes';r72='AspisR72Sampler.Types';groups={'OwnedAudit52':[],'ModelAudit52':[],'NeutralAudit52':[]};names={k:set() for k in groups};checks=[]
for m,v in accepted.items():
 q=closure(m);assert not {owned,r72}<=q,m
 group='OwnedAudit52' if owned in q else 'ModelAudit52' if r72 in q else 'NeutralAudit52'
 groups[group].append(m)
 for ax in v['axioms']:
  assert 'sorryAx' not in ax,ax
  names[group].add(re.match(r"'([^']+)'",ax)[1])
 checks.append(dict(module=m,owned_types=owned in q,r72_types=r72 in q,group=group))
for k,mods in groups.items():
 extra=['R1Z.PV_RunJoin_CircleAudit51'] if k=='OwnedAudit52' else ['R1Z.PV_RunJoin_CombinedAudit51'] if k=='ModelAudit52' else []
 s='\n'.join('import '+m for m in extra+sorted(mods))+'\n\n'+''.join('#print axioms '+n+'\n' for n in sorted(names[k]))
 (L/('PV_RunJoin_'+k+'.lean')).write_text(s)
(E/'audit-design.json').write_text(json.dumps(dict(groups=groups,printed_names={k:sorted(v) for k,v in names.items()},source_import_checks=checks,no_colliding_types_coimported=True),indent=2)+'\n')
print({k:dict(modules=len(v),printed_names=len(names[k])) for k,v in groups.items()})
