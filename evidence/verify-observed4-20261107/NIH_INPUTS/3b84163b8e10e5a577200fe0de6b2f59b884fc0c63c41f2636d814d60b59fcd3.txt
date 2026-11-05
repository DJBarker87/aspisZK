from pathlib import Path
import hashlib,json,shutil
B=Path(__file__).resolve().parent;D=Path('/home/dombarker/project-offloads/codex-cx-prepared-claim-cache-20261104/NIH_seed_20261107/NIH_NDN');D.mkdir(exist_ok=False)
x=json.loads((B/'NIH_NDN_PINS.json').read_text());paths=json.loads((B/'NIH_PATHS.json').read_text());rows=[]
for old,v in x['selected_objects'].items():
 marker=next(k for k in ['/NDE_objects/','/NDN_objects/'] if k in old);rel=old.split(marker,1)[1]
 candidates=[Path(old)]+[Path(root)/rel for root in paths]+[Path('/home/dombarker/project-offloads/codex-cx-front2-cache-20261028')/rel]
 source=next((p for p in candidates if p.is_file() and hashlib.sha256(p.read_bytes()).hexdigest()==v['sha256']),None)
 assert source is not None,('missing pinned legacy object',old)
 dest=D/rel;dest.parent.mkdir(parents=True,exist_ok=True)
 if dest.exists():assert hashlib.sha256(dest.read_bytes()).hexdigest()==v['sha256']
 else:shutil.copyfile(source,dest)
 rows.append(dict(path=str(dest),source=str(source),sha256=v['sha256'],bytes=dest.stat().st_size))
paths.insert(2,str(D));(B/'NIH_PATHS.json').write_text(json.dumps(paths,indent=2)+'\n');(B/'NIH_NDN_SEED.json').write_text(json.dumps(dict(files=rows,total_bytes=sum(r['bytes'] for r in rows)),indent=2)+'\n');print('NDN seed bytes',sum(r['bytes'] for r in rows))
