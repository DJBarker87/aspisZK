from pathlib import Path
import json,hashlib,shutil
B=Path(__file__).resolve().parent
paths=json.loads((B/'NIX_PATHS.json').read_text());fallback=[p for p in json.loads((B/'NIX_NIM_ORIGINAL_PATHS.json').read_text()) if '-cache-'in p]
D=Path('/home/dombarker/project-offloads/codex-cx-prepared-claim-cache-20261104/NIX_seed_20261107/NIM_dependencies');D.mkdir(exist_ok=True)
table={r['module']:r['imports'] for r in map(json.loads,(B/'NIX_NIM_EXPECTED_IMPORTS.jsonl').read_text().splitlines())};todo=['NIM_NHJ_COMBINED_IMPORT','NIM_NHY_COMBINED_IMPORT'];seen=set();copied=[]
while todo:
 n=todo.pop()
 if n in seen:continue
 seen.add(n);todo+=table.get(n,[]);rel=n.replace('.','/')+'.olean'
 if any(Path(p,rel).is_file() for p in paths):continue
 if (D/rel).is_file():continue
 source=next((Path(p,rel) for p in fallback if Path(p,rel).is_file()),None);assert source is not None,('missing retained dependency',n)
 for suffix in ['','.private','.server']:
  p=Path(str(source)+suffix)
  if p.is_file():
   dest=Path(str(D/rel)+suffix);dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,dest);copied.append(dict(source=str(p),path=str(dest),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
 p=source.with_suffix('.ir')
 if p.is_file():
  dest=(D/rel).with_suffix('.ir');dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,dest);copied.append(dict(source=str(p),path=str(dest),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
paths.insert(1,str(D));(B/'NIX_PATHS.json').write_text(json.dumps(paths,indent=2)+'\n');(B/'NIX_NIM_DEPENDENCIES.json').write_text(json.dumps(dict(reachable_modules=len(seen),total_bytes=sum(r['bytes'] for r in copied),files=copied),indent=2)+'\n');print('Copied missing retained NIM objects only',len(copied),sum(r['bytes'] for r in copied))
