"""adopted by owner decision D502/D478. Verify the final cached focused manifest."""
from pathlib import Path
import json,hashlib,re,subprocess,shlex
E=Path('evidence/pv-evh-20261029');H='/home/dombarker/project-offloads/codex-pv-evh-20261029'
receipts=[json.load(open(q)) for q in E.glob('receipt-*.json')]
accepted={r['target']:r for r in sorted(receipts,key=lambda r:r['attempt']) if r['accepted']}
expected={p.stem for p in Path('lean').glob('PV_EVH_*.lean') if p.stem!='PV_EVH_FixtureConsumer'}
assert set(accepted)==expected,(expected-set(accepted),set(accepted)-expected)
checks={};modules=[];toolchains=set();prefixes=set()
for m in sorted(expected):
 r=accepted[m];p=Path('lean/'+m+'.lean');b=p.read_bytes()
 assert hashlib.sha256(b).hexdigest()==r['source_sha256'],m
 assert subprocess.check_output(['git','show','HEAD:'+str(p)])==b
 prep=json.load(open(E/('prepare-'+m+'.json')))['result']
 toolchains.add(prep['toolchain']);prefixes.add(prep['LEAN_PATH'])
 for c in prep['project_checks']+prep['external_checks']:
  assert c['path'] not in checks or checks[c['path']]==c['sha256'],c['path']
  checks[c['path']]=c['sha256']
 checks[H+'/objects/'+m+'.olean']=r['object_sha256']
 modules.append(dict(module=m,path=str(p),source_sha256=r['source_sha256'],
                     accepted_attempt=r['attempt'],object_sha256=r['object_sha256']))
assert len(toolchains)==len(prefixes)==1
code='''import sys,json,pathlib,hashlib
checks=json.load(sys.stdin);bad=[]
for name,expected in checks.items():
 p=pathlib.Path(name)
 if not p.exists() or hashlib.sha256(p.read_bytes()).hexdigest()!=expected:bad.append(name)
print(json.dumps(dict(checked=len(checks),mismatches=bad)))
assert not bad
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(checks),text=True,capture_output=True)
assert r.returncode==0,r.stderr+r.stdout
out=(E/'out-70498.log').read_text()
theorems=[]
for p in Path('lean').glob('PV_EVH_*.lean'):
 if p.stem=='PV_EVH_FixtureConsumer':continue
 for n in re.findall(r'^theorem (\w+)',p.read_text(),re.M):
  assert re.search(r"'[^']*\."+n+r"' (?:depends on axioms:|does not depend on any axioms)",out),n
  theorems.append(dict(module=p.stem,theorem=n))
assert len(theorems)==len({x['theorem'] for x in theorems})
result=dict(status='PASS: final focused cached manifest; not a native release replay',
 revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
 modules=modules,theorems=theorems,host_object_check=json.loads(r.stdout),
 toolchain=next(iter(toolchains)),LEAN_PATH=next(iter(prefixes)),
 lead_only_consumer='PV_EVH_FixtureConsumer: NOT COMPILED',
 deployment_instance_status='Native event-producing source selection and links remain OPEN')
(E/'final-manifest.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS:',len(modules),'modules;',len(theorems),'theorems;',json.loads(r.stdout)['checked'],'object hashes')
