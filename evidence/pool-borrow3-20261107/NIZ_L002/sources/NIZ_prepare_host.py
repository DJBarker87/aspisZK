from pathlib import Path
import sys,json,subprocess,hashlib
B=Path(__file__).resolve().parent
sys.path.insert(0,str(B/'NIZ_stage'))
import NHR_stage
S=B/'NIZ_src'
manifest=NHR_stage.stage(S)
for n,t in json.loads((B/'NIZ_INCLUDES.json').read_text()).items():
 p=S/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(t)
subprocess.run(['git','apply',str(B/'NIZ_KMX_copy_stubs.patch')],cwd=S,check=True)
print(json.dumps(dict(staged_files=len(manifest['files']),frozen_revision=manifest['revision'],source_bytes=sum(p.stat().st_size for p in S.rglob('*') if p.is_file()),cargo_target_dir=str(B/'NIZ_target'),lock_sha256=hashlib.sha256((S/'Cargo.lock').read_bytes()).hexdigest())))
