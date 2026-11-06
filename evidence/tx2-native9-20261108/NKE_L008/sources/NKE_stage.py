"""Stage pinned NHR transport into this job's scratch; no extraction performed."""
from pathlib import Path
import importlib.util,hashlib,json,subprocess,sys
sys.dont_write_bytecode=True
B=Path(__file__).resolve().parent
P=B.parent/'codex-cx-extract-stage-20261106'
spec=importlib.util.spec_from_file_location('NHR_stage',P/'NHR_stage.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
manifest=m.stage(B/'NKE_src')
patch=B/'NKE_KMX.patch'
assert hashlib.sha256(patch.read_bytes()).hexdigest()=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
r=subprocess.run(['patch','-p1','--batch','--forward','-i',str(patch)],cwd=B/'NKE_src')
assert r.returncode==0
(B/'NKE_STAGE.json').write_text(json.dumps(dict(files=len(manifest['files']),frozen=m.REV,manifest_sha256=hashlib.sha256((P/'NHR_STAGING_MANIFEST.json').read_bytes()).hexdigest(),patch_sha256=hashlib.sha256(patch.read_bytes()).hexdigest(),extraction_runs=0),indent=2))

S=B/'NKE_src'
files={str(p.relative_to(S)):hashlib.sha256(p.read_bytes()).hexdigest() for root in ['crates','programs'] for p in (S/root).rglob('*') if p.is_file()}
(B/'NKE_SOURCE_PINS.json').write_text(json.dumps(files,indent=2))
