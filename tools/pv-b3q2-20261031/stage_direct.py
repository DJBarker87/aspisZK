from pathlib import Path
import shutil,tarfile,json,hashlib,tomllib
H=Path('/home/dombarker/project-offloads/codex-pv-b3q2-20261031');B=H.parent/'codex-pv-b3p6-20261028/source';O=H/'direct-source';assert not O.exists()
shutil.copytree(B,O,ignore=shutil.ignore_patterns('target','charon-target','.git','.lake','node_modules','lean-objects'))
a=H/'pv-b3q2-audit-member.tar'
with tarfile.open(a)as t:
 for m in t.getmembers():
  assert not m.name.startswith('/')and'..'not in Path(m.name).parts and not m.issym()and not m.islnk(),m.name
 t.extractall(O,filter='data')
ws=tomllib.loads((O/'Cargo.toml').read_text())['workspace']['members'];missing=[s for s in ws if not(O/s/'Cargo.toml').exists()]
x=dict(source=str(B),private_copy=str(O),archive_sha256=hashlib.sha256(a.read_bytes()).hexdigest(),workspace_members=ws,missing=missing,source_modified=False,old_scope='N77114 failed before translation; missing workspace manifest')
(H/'direct-source-staging.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps(x));assert not missing,missing
