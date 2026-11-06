from pathlib import Path
import hashlib,json,shutil,subprocess,os
E=Path(__file__).resolve().parent
P=Path('/home/dombarker/project-offloads/codex-cx-extract-stage-20261106')
for name in ['NHR_FROZEN_PAYLOAD.json.xz','NHR_FROZEN_PAYLOAD.json.sha256','NHR_STAGING_MANIFEST.json','NHR_OPACITY.json']:
 t=E/name
 if not t.exists(): t.symlink_to(P/name)
 assert t.resolve()==(P/name).resolve()
cache=Path('/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104/NJA_20261107');cache.mkdir(exist_ok=True)
root=Path('/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NIU_20261107/NIU_exports_20261107')
files=[]
for p in sorted(root.rglob('*')):
 if not p.is_file():continue
 q=cache/p.relative_to(root);q.parent.mkdir(parents=True,exist_ok=True)
 h=hashlib.sha256(p.read_bytes()).hexdigest()
 if not q.exists():shutil.copy2(p,q)
 assert hashlib.sha256(q.read_bytes()).hexdigest()==h
 files.append(dict(source=str(p),destination=str(q),sha256=h,bytes=p.stat().st_size))
(E/'NJA_SEED.json').write_text(json.dumps(dict(files=files,bytes=sum(x['bytes'] for x in files),first_seed=str(root),cargo_target=os.environ['CARGO_TARGET_DIR']),indent=2)+'\n')
raise SystemExit(subprocess.call(['python3','NJA_stage.py','--check','--workspace','NJA_workspace','--out','NJA_preflight']))
