"""Read-only search of Stream B caches for the 200 retained prerequisites."""
import pathlib,json,subprocess,shlex
R=pathlib.Path(__file__).resolve().parents[2];E=R/'evidence/pv-reach-20261027/resume8'
rows=json.loads((E.parent/'resume7/remaining-cohort-prerequisites.json').read_text())
(E/'prerequisites-before.json').write_text(json.dumps(rows,indent=2)+'\n')
(E/'prerequisites-before.txt').write_text('\n'.join(r['module'] for r in rows)+'\n')
script='''import pathlib,json,sys,os
rows=json.load(sys.stdin);want={r['module'].replace('.','/')+'.olean':r['module'] for r in rows};out={r['module']:[] for r in rows};base=pathlib.Path('/home/dombarker/project-offloads')
for root in sorted(base.glob('codex-pv-*')):
 if root.name=='codex-pv-reach-20261027':continue
 for dp,ds,fs in os.walk(root):
  ds[:]=[d for d in ds if d not in ['target','target-charon','.git','node_modules']]
  for f in fs:
   if not f.endswith('.olean'):continue
   p=pathlib.Path(dp)/f
   for rel,m in want.items():
    if str(p).endswith('/'+rel):out[m].append(str(p))
print(json.dumps(out,indent=2))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(script)],input=json.dumps(rows),text=True,capture_output=True,check=True)
(E/'stream-b-candidate-objects.json').write_text(r.stdout)
d=json.loads(r.stdout);print('modules with candidates',sum(bool(v) for v in d.values()),'without',sum(not v for v in d.values()))
print(json.dumps({k:v for k,v in d.items() if v},indent=2))
