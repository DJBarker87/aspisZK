from pathlib import Path
import ast,json,subprocess,hashlib
p=Path(__file__).resolve().parent;s=ast.parse((p/'NLH_run.py').read_text());H=next(ast.literal_eval(n.value)for n in ast.walk(s)if isinstance(n,ast.Assign)and any(isinstance(t,ast.Name)and t.id=='H'for t in n.targets))
modules=sorted(json.loads((p/'NLH_GATE_SOURCES.json').read_text())['passed'])+['NLH_COMBINED_IMPORT'];env=json.loads((p/'NLH_ENV.json').read_text());rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip();sources={m:hashlib.sha256((p/(m+'.lean')).read_bytes()).hexdigest()for m in modules}
code='''from pathlib import Path
import json,shutil,hashlib
b=Path('/home/dombarker/project-offloads/codex-cx-terminal6-20261110');out=b/'NLH_exports_20261110';out.mkdir(exist_ok=True)
modules=MODULES;sources=SOURCES;rows=[]
for m in modules:
 for src in [b/(m+'.lean'),b/'NLH_objects'/(m+'.olean')]:
  assert src.is_file(),str(src)
  raw=src.read_bytes();digest=hashlib.sha256(raw).hexdigest()
  if src.suffix=='.lean':assert digest==sources[m]
  target=out/src.name
  if target.exists():assert target.read_bytes()==raw,str(target)
  else:shutil.copyfile(src,target)
  rows.append(dict(name=src.name,bytes=len(raw),sha256=digest))
x=dict(path=str(out),source_revision=REV,modules=len(modules),files=rows,total_bytes=sum(r['bytes']for r in rows),lean_path=[str(out)]+ENV['LEAN_PATH'].split(':'),seed_manifests=['NLH_SEED.json','NLH_SEED_INPUTS.json'],authority='candidate export; authoritative adoption waits next ledger gate',security_target_established=False)
(out/'NLH_EXPORT.json').write_text(json.dumps(x,indent=1)+'\\n');print(json.dumps(x))
'''.replace('MODULES',repr(modules)).replace('SOURCES',repr(sources)).replace('REV',repr(rev)).replace('ENV',repr(env))
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input=code,text=True,capture_output=True);assert r.returncode==0,(r.returncode,r.stderr);x=json.loads(r.stdout);(p/'NLH_EXPORT.json').write_text(json.dumps(x,indent=1)+'\n');print(json.dumps(dict(export=x['path'],modules=x['modules'],bytes=x['total_bytes'])))
