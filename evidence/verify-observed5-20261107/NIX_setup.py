from pathlib import Path
import subprocess,json,shutil,hashlib
import NIX_stage as stage
B=Path(__file__).resolve().parent
r=subprocess.run(['python3','NIX_stage.py','--check','--workspace','NIX_src','--out','NIX_preflight'],cwd=B)
assert r.returncode==0
# Frozen corpus staging is complete before any scratch harness is added.
(B/'NIX_SETUP.json').write_text(json.dumps(dict(frozen_revision=stage.REV,source_bytes=sum(p.stat().st_size for p in (B/'NIX_src').rglob('*') if p.is_file()),cargo_target_dir=str(B/'NIX_target'),stage_sha256=hashlib.sha256((B/'NIX_stage.py').read_bytes()).hexdigest()),indent=2))
print('NIX frozen staging/check passed')
