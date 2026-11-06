from pathlib import Path
import json,hashlib,shutil
B=Path(__file__).resolve().parent;x=json.loads((B/'NJG_NIU_EXPORT_INPUT.json').read_text());P=Path(x['export']);D=Path('/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104/NJG_NIU_20261107');D.mkdir()
pins=[]
for v in x['files']:
 p=Path(v['path']);assert hashlib.sha256(p.read_bytes()).hexdigest()==v['sha256'];q=D/p.relative_to(P);q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q);pins.append(dict(source=str(p),path=str(q),sha256=v['sha256'],bytes=q.stat().st_size))
old=json.loads((B/'NJG_PATHS.json').read_text());more=[str(D)]+json.loads((B/'NJG_NIU_PATHS_INPUT.json').read_text());paths=list(dict.fromkeys(old[:2]+more+old[2:]));(B/'NJG_PATHS.json').write_text(json.dumps(paths,indent=2))
(B/'NJG_NIU_SEED.json').write_text(json.dumps(dict(files=pins,total_bytes=sum(v['bytes'] for v in pins),cargo_target_dir=str(B/'NJG_target')),indent=2));print('NJG NIU retained export copied with original hashes')
