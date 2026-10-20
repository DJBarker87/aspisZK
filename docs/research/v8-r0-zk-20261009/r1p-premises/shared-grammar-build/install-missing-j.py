"""Populate absent unified sources only; refuse every differing existing source."""
import hashlib,json,pathlib,subprocess
repo=pathlib.Path.cwd(); host='dombarker@100.108.41.90'; j='/home/dombarker/project-offloads/aspis-joint-20261019'
mp=repo/'docs/research/v8-r0-zk-20261009/t2b2b/build-integration/manifest-5-shared-grammar.json'
man=json.loads(mp.read_text()); probe='''import hashlib,json,pathlib
j=pathlib.Path('/home/dombarker/project-offloads/aspis-joint-20261019')
m=json.loads((j/'evidence/manifest-5-shared-grammar.json').read_text()); missing=[]; mismatch=[]
for e in m['order']:
 p=j/'sources'/(e['module'].replace('.','/')+'.lean')
 if not p.exists(): missing.append(e)
 elif hashlib.sha256(p.read_bytes()).hexdigest()!=e['sha256']: mismatch.append(e['module'])
print(json.dumps({'missing':missing,'mismatch':mismatch}))
'''
subprocess.run(['scp',str(mp),f'{host}:{j}/evidence/manifest-5-shared-grammar.json'],check=True)
r=json.loads(subprocess.check_output(['ssh',host,'python3 -'],input=probe,text=True)); assert not r['mismatch'],r
for e in r['missing']:
 dest=j+'/sources/'+e['module'].replace('.','/')+'.lean'
 subprocess.run(['ssh',host,'mkdir','-p',str(pathlib.PurePosixPath(dest).parent)],check=True)
 subprocess.run(['scp',str(repo/e['source']),host+':'+dest],check=True)
print(json.dumps({'installed':[e['module'] for e in r['missing']],'overwritten':[]},indent=2))
