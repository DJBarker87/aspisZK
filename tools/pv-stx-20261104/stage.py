"""Stage only new PV_STX modules; verify the existing external authority first."""
from pathlib import Path
import hashlib,json,subprocess,shlex,sys,re
E=Path('evidence/pv-stx-20261104'); H='/home/dombarker/project-offloads/codex-pv-stx-20261104'
base=json.loads(Path('evidence/pv-evh4-20261029/prepare-PV_EVH_World.json').read_text())['result']
authority=json.loads((E/'external-authority.json').read_text())
assert {v['module']:v['sha256'] for v in base['external_checks']}=={v['module'].replace('/','.'):v['object_sha256'] for v in authority}
m=sys.argv[1];assert m.startswith('PV_STX_'); raw=Path('lean/'+m+'.lean').read_bytes()
rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
assert subprocess.check_output(['git','show',rev+':lean/'+m+'.lean'])==raw
checks=base['project_checks'].copy()
for v in checks:
 if 'source' in v:
  src=v['source']; old=subprocess.check_output(['git','show',src['revision']+':'+src['path']]);assert hashlib.sha256(old).hexdigest()==src['source_sha256']
  assert subprocess.check_output(['git','show',rev+':'+src['path']])==old,('source changed',v['module'])
latest={}
for p in sorted(E.glob('receipt-*.json')):
 r=json.loads(p.read_text())
 if r.get('accepted'):
  src=Path('lean/'+r['target']+'.lean')
  if src.exists() and hashlib.sha256(src.read_bytes()).hexdigest()==r['source_sha256']:
   latest[r['target']]=r
for r in latest.values():
 checks.append(dict(module=r['target'],sha256=r['object_sha256'],path=H+'/objects/'+r['target']+'.olean'))
known={x['module'] for x in checks}|{x['module'] for x in base['external_checks']}
assert set(re.findall(r'^import (\S+)',raw.decode(),re.M))<=known
payload=dict(H=H,module=m,source=raw.decode(),sha256=hashlib.sha256(raw).hexdigest(),revision=rev,
 external=base['external_checks'],checks=checks,roots=[H+'/objects']+base['LEAN_PATH'].split(':'),toolchain=base['toolchain'])
code=r'''
from pathlib import Path
import hashlib,json,sys,subprocess
x=json.load(sys.stdin);h=Path(x['H']);(h/'objects').mkdir(exist_ok=True);(h/'sources').mkdir(exist_ok=True);(h/'evidence').mkdir(exist_ok=True)
env=json.load(open('/home/dombarker/project-offloads/codex-pv-evh-20261029/J.json'))
assert subprocess.check_output([env['LEAN'],'--githash'],text=True).strip()==x['toolchain']
env['LEAN_PATH']=':'.join(x['roots']);roots=list(map(Path,x['roots']));resolved=[]
for v in x['external']+x['checks']:
 m=v['module'];ns=m.split('.')[0]
 root=next(r for r in roots if (r/ns).is_dir() or ('.' not in m and (r/(m+'.olean')).is_file()))
 q=root/(m.replace('.','/')+'.olean');assert q.is_file(),('namespace shadow',m,str(q))
 digest=hashlib.sha256(q.read_bytes()).hexdigest();assert digest==v['sha256'],('object hash',m,str(q))
 resolved.append(dict(module=m,path=str(q),sha256=digest))
(h/'J.json').write_text(json.dumps(env,indent=2)+'\n')
(h/'sources'/(x['module']+'.lean')).write_text(x['source'])
print(json.dumps(dict(source_sha256=x['sha256'],source_revision=x['revision'],toolchain=x['toolchain'],LEAN_PATH=env['LEAN_PATH'],effective_resolution=resolved,external_authority='h4 pv-replay-20261027 (inherited verified evh4 manifest)',project_dependencies=x['checks'],shared_written=False)))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(payload),capture_output=True,text=True)
(E/('prepare-'+m+'.json')).write_text(json.dumps(dict(exit=r.returncode,stderr=r.stderr,result=json.loads(r.stdout) if r.returncode==0 else r.stdout),indent=2)+'\n')
assert r.returncode==0,r.stderr
print('staged',m)
