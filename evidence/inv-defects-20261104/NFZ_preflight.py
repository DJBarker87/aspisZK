"""Byte-exact dry collection, including binary and recursive literal includes."""
from pathlib import Path
import json,lzma,hashlib,base64,subprocess,tempfile,posixpath,re
E=Path(__file__).resolve().parent;R=E.parents[1]
sha=lambda b:hashlib.sha256(b).hexdigest()
pins=json.loads((E/'NFZ_SOURCE_PINS.json').read_text())
t=json.loads(lzma.open(E/'NFZ_FROZEN_SOURCE.json.xz').read());b=json.loads(lzma.open(E/'NFZ_FROZEN_BINARY.json.xz').read())
files={**{p:s.encode() for p,s in t.items()},**{p:base64.b64decode(s,validate=True) for p,s in b.items()}}
assert set(files)==set(pins['files'])
includes=[]
with tempfile.TemporaryDirectory(prefix='NFZ-stage-') as tmp:
 stage=Path(tmp)
 for p,data in files.items():
  assert not Path(p).is_absolute() and '..' not in Path(p).parts
  assert sha(data)==pins['files'][p]
  assert data==subprocess.check_output(['git','show',pins['revision']+':'+p],cwd=R)
  dest=stage/p;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(data)
 for p in files:
  assert (stage/p).read_bytes()==files[p]
  try:s=files[p].decode()
  except UnicodeDecodeError:continue
  for rel in re.findall(r'include(?:_str|_bytes)?!\s*\(\s*"([^"]+)"',s):
   q=posixpath.normpath(posixpath.dirname(p)+'/'+rel)
   assert q in files and (stage/q).read_bytes()==files[q]
   includes.append(dict(source=p,target=q,sha256=sha(files[q])))
 result=dict(result='PASS',frozen_revision=pins['revision'],text_files=len(t),binary_files=len(b),literal_includes=includes,payload_sha256=sha((E/'NFZ_FROZEN_SOURCE.json.xz').read_bytes()),binary_payload_sha256=sha((E/'NFZ_FROZEN_BINARY.json.xz').read_bytes()),pins_sha256=sha((E/'NFZ_SOURCE_PINS.json').read_bytes()),local_dry_collection=dict(byte_identical=True,file_count=len(files),all_transitive_literal_includes=True,staging_tree_removed=True))
 (E/'NFZ_PAYLOAD_PREFLIGHT.json').write_text(json.dumps(result,indent=1)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='literal_includes'}))
