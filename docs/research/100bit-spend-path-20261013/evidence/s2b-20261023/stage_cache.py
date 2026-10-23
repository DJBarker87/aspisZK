#!/usr/bin/env python3
"""Read cached import headers; stage a private Linux overlay without rebuilding."""
import hashlib,importlib.util,json,pathlib,re,subprocess
base=pathlib.Path(__file__).resolve().parents[2]
out=pathlib.Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('headers','/tmp/check-olean-import-closure.py')
headers=importlib.util.module_from_spec(spec);spec.loader.exec_module(headers)
command=json.loads((base/'evidence/s126-current-caller-20261021/s2-sdk-ready-caller-v2/command.json').read_text())
p=next(s.split('=',1)[1] for s in command['command'] if s.startswith('LEAN_PATH='))
lead=json.loads((base/'evidence/s2-interface-20261022/S2LeadInterface-3/command.json').read_text())
roots=list(dict.fromkeys(pathlib.Path(x) for x in (p+':'+lead['lean_path']).split(':')))
seeds=['S2SdkReadyStatementV1','S2LeadInterface']
queue=seeds.copy();seen={}
while queue:
 m=queue.pop()
 if m in seen:continue
 rel=pathlib.Path(*m.split('.')).with_suffix('.olean')
 path=next((r/rel for r in roots if (r/rel).is_file()),None)
 if path is None:raise RuntimeError('Missing '+m)
 ds=headers.imports(path)
 seen[m]={'path':str(path),'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'size':path.stat().st_size,'imports':ds}
 queue.extend(ds)
(out/'cache-manifest.json').write_text(json.dumps({'seeds':seeds,'modules':seen},indent=2)+'\n')
remote='/home/dombarker/project-offloads/codex-cx-s2b-20261023'
subprocess.run(['ssh','dombarker@100.108.41.90','mkdir','-p',remote+'/objects',remote+'/sources'],check=True)
groups={}
for m,item in seen.items():
 path=pathlib.Path(item['path']);rel=pathlib.Path(*m.split('.')).with_suffix('.olean')
 root=str(path)[:-len(str(rel))]
 # Linux standard library uses the pinned host toolchain, not macOS objects.
 if '/.elan/toolchains/' in root:continue
 groups.setdefault(root,[]).append(str(rel))
for root,files in groups.items():
 subprocess.run(['rsync','-aL','--files-from=-',root,'dombarker@100.108.41.90:'+remote+'/objects/'],input='\n'.join(files)+'\n',text=True,check=True)
print(json.dumps({'modules':len(seen),'non_sysroot_bytes':sum(i['size'] for i in seen.values() if '/.elan/toolchains/' not in i['path'])}))
