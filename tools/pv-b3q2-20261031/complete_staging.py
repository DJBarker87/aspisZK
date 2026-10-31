from pathlib import Path
import tarfile,json,hashlib,tomllib
H=Path('/home/dombarker/project-offloads/codex-pv-b3q2-20261031');O=H/'direct-source';a=H/'pv-b3q2-xtask.tar';assert not(O/'xtask').exists()
with tarfile.open(a)as t:
 for m in t.getmembers():assert not m.name.startswith('/')and'..'not in Path(m.name).parts and not m.issym()and not m.islnk()
 t.extractall(O,filter='data')
ws=tomllib.loads((O/'Cargo.toml').read_text())['workspace']['members'];missing=[s for s in ws if not(O/s/'Cargo.toml').exists()]
x=dict(private_copy=str(O),archive_sha256=hashlib.sha256(a.read_bytes()).hexdigest(),missing=missing,source_modified=False,previous_scope='N77115 detected missing xtask before any compile')
(H/'direct-source-staging-complete.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps(x));assert not missing
