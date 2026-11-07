from NMX_formal import *
base=E.parent/'libb-20261111';rows=[json.loads(l) for l in (base/'LIBB_ATTEMPTS.jsonl').read_text().splitlines()];accepted={}
for r in rows:
 m=r.get('module','');p=base/(m+'.lean')
 if r.get('kind')=='lean' and r.get('exit_status')==0 and m.startswith('LIBB_') and p.is_file() and sha(p.read_bytes()) in r.get('source_hashes',{}).values():accepted[m]=r
needed=set()
def visit(m):
 if m in needed:return
 assert m in accepted,('no current accepted supplying source',m)
 needed.add(m)
 for dep in re.findall(r'^import (LIBB_\w+)',(base/(m+'.lean')).read_text(),re.M):visit(dep)
visit('LIBB_V2Star')
roots=json.loads((base/'LIBB_L344/receipt.json').read_text())['env']['LEAN_PATH'].split(':')
manifest={m:dict(attempt=accepted[m]['attempt'],source_sha256=sha((base/(m+'.lean')).read_bytes())) for m in sorted(needed)}
script='''from pathlib import Path
import os,json,hashlib,shutil
b=Path.cwd();roots=json.loads(%r);manifest=json.loads(%r);out=[]
for m,acceptance in manifest.items():
 p=next((Path(r)/(m+'.olean') for r in roots if (Path(r)/(m+'.olean')).is_file()),None);assert p,m
 for z in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if not z.is_file():continue
  h=hashlib.sha256(z.read_bytes()).hexdigest();old=b/'NMX_LIBB_seed'/z.name
  if old.exists():assert hashlib.sha256(old.read_bytes()).hexdigest()==h,('published old component drift',m)
  q=b/'NMX_LIBB_gate_seed'/z.name;q.parent.mkdir(exist_ok=True)
  if q.exists():assert hashlib.sha256(q.read_bytes()).hexdigest()==h,q
  else:shutil.copy2(z,q)
  out.append(dict(module=m,source=str(z),copy=str(q),sha256=h,bytes=q.stat().st_size,**acceptance))
(b/'NMX_LIBB_GATE_SEED.json').write_text(json.dumps(out,indent=1)+'\\n');print(json.dumps(dict(modules=len(manifest),files=len(out),deletions=0)))
''' % (json.dumps(roots),json.dumps(manifest))
r=run('NMX_L1061','inspect','NMX_LIBB_gate_seed',['python3','NMX_seed_libb_gate_host.py'],{'NMX_seed_libb_gate_host.py':script});assert r['exit_status']==0
z=ssh('cat '+B+'/NMX_LIBB_GATE_SEED.json');assert z.returncode==0
(E/'NMX_LIBB_GATE_SEED.json').write_text(z.stdout)
env=json.loads((E/'NMX_R3_REGISTRY_ENV.json').read_text());env['LEAN_PATH']=':'.join(dict.fromkeys([B+'/NMX_LIBB_gate_seed']+env['LEAN_PATH'].split(':')));(E/'NMX_R3_REGISTRY_ENV.json').write_text(json.dumps(env,indent=1)+'\n')
