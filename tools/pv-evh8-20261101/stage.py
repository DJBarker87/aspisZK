"""Stage a new module against the already verified SAME small import closure.
No builds or changes to external/shared sources or objects."""
from pathlib import Path
import json,subprocess,sys,hashlib,re,shlex
E=Path('evidence/pv-evh8-20261101'); OLD=Path('evidence/pv-evh4-20261029');H='/home/dombarker/project-offloads/codex-pv-evh-20261029'
module=sys.argv[1];assert module.startswith('PV_EVH_')
sha=lambda b:hashlib.sha256(b).hexdigest()
base=json.load(open(OLD/'prepare-PV_EVH_World.json'))['result']
rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
checks=base['project_checks'].copy();known={v['module'] for v in checks}
for v in checks:
 if 'source' in v:
  s=v['source'];raw=subprocess.check_output(['git','show',s['revision']+':'+s['path']]);assert sha(raw)==s['source_sha256']
  current=subprocess.check_output(['git','show',rev+':'+s['path']]);assert current==raw,('source changed',v['module'])
# Same recorded runjoin61 project cohort; no library authority extension.
extension=E/'source-binding-extension.json'
if extension.exists():
 ext=json.loads(extension.read_text())
 assert ext['LEAN_PATH']==base['LEAN_PATH']
 changed=set(subprocess.check_output(['git','diff','--name-only',ext['verified_source_revision'],rev],text=True).splitlines())
 assert not changed.intersection(v['source']['path'] for v in ext['project_checks']), 'extended source changed'
 for v in ext['project_checks']:
  if v['module'] not in known:
   checks.append(v);known.add(v['module'])
for p in sorted(OLD.glob('receipt-*.json'))+sorted(Path('evidence/pv-evh5-20261029').glob('receipt-*.json'))+sorted(E.glob('receipt-*.json')):
 r=json.loads(p.read_text())
 if not r.get('accepted'):continue
 m=r['target'];path='lean/'+m+'.lean';raw=subprocess.check_output(['git','show',rev+':'+path])
 assert sha(raw)==r['source_sha256']
 prep=json.load(open(p.parent/('prepare-'+m+'.json')))['result']
 assert prep['LEAN_PATH']==base['LEAN_PATH'] and prep['toolchain']==base['toolchain']
 assert {x['module']:x['sha256'] for x in prep['project_checks']}=={x['module']:x['sha256'] for x in checks if x['module'] in {y['module'] for y in prep['project_checks']}}
 if m not in known:
  checks.append(dict(module=m,path=H+'/objects/'+m+'.olean',sha256=r['object_sha256'],source=dict(path=path,revision=rev,source_sha256=r['source_sha256'])))
  known.add(m)
source=Path('lean/'+module+'.lean').read_bytes();assert source==subprocess.check_output(['git','show',rev+':lean/'+module+'.lean'])
imports=re.findall(r'^import (\S+)',source.decode(),re.M);assert set(imports)<=known,('new import needs full prepare',set(imports)-known)
payload=dict(checks=checks,external=base['external_checks'],roots=base['LEAN_PATH'].split(':'),H=H,module=module,source=source.decode(),sha256=sha(source),revision=rev,toolchain=base['toolchain'])
code=r'''
import json,sys,pathlib,hashlib,subprocess
x=json.load(sys.stdin);H=pathlib.Path(x['H']);env=json.load(open(H/'J.json'))
assert env['LEAN_PATH'].split(':')==x['roots'];assert subprocess.check_output([env['LEAN'],'--githash'],text=True).strip()==x['toolchain']
roots=list(map(pathlib.Path,x['roots']));effective=[]
def resolve(m):
 ns=m.split('.')[0]
 root=next(r for r in roots if (r/ns).is_dir() or ('.' not in m and (r/(m+'.olean')).is_file()))
 q=root/(m.replace('.','/')+'.olean');assert q.is_file(),('h6 shadow',m,str(q));return q
for v in x['checks']+x['external']:
 q=resolve(v['module']);digest=hashlib.sha256(q.read_bytes()).hexdigest();assert digest==v['sha256'],('object changed',v['module'])
 if 'source' in v:
  assert not q.is_symlink(),('h6 plain copy',v['module'])
 effective.append(dict(module=v['module'],path=str(q),sha256=digest))
(H/('sources/'+x['module']+'.lean')).write_text(x['source'])
print(json.dumps(dict(project_checks=x['checks'],external_checks=x['external'],effective_resolution=effective,toolchain=x['toolchain'],LEAN_PATH=env['LEAN_PATH'],source_revision=x['revision'],source_sha256=x['sha256'],shared_written=False)))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(payload),text=True,capture_output=True)
result=dict(exit=r.returncode,stderr=r.stderr,result=json.loads(r.stdout) if r.returncode==0 else r.stdout)
prior=E/('prepare-'+module+'.json')
if prior.exists():
 archive=E/'prepare-history';archive.mkdir(exist_ok=True)
 (archive/(sha(prior.read_bytes())+'.json')).write_bytes(prior.read_bytes())
(E/('prepare-'+module+'.json')).write_text(json.dumps(result,indent=2)+'\n');assert r.returncode==0,r.stderr+r.stdout
print('PASS same-cohort stage',module)
