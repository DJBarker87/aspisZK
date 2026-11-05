"""One changed-opacity extraction via exact private NHR_stage; no shared writes."""
from pathlib import Path
import sys,importlib.util,hashlib,json,types,lzma,base64
sys.dont_write_bytecode=True
B=Path(__file__).resolve().parent;P=B.parent/'codex-cx-extract-stage-20261106'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins=json.loads((B/'NIL_EXTRACT_INPUT_PINS.json').read_text())
assert sha(B/'NIL_NHR_stage.py')==sha(P/'NHR_stage.py')==pins['stager_sha256']
assert sha(B/'NIL_EXTRACT_OPACITY.json')==pins['opacity_sha256']
for name in ['NHR_STAGING_MANIFEST.json','NHR_FROZEN_PAYLOAD.json.xz','NHR_FROZEN_PAYLOAD.json.sha256']:
 link=B/name
 if not link.exists():link.symlink_to(P/name)
 assert link.resolve()==(P/name).resolve()
link=B/'NHR_target'
if not link.exists():link.symlink_to(B/'NIL_target',target_is_directory=True)
assert link.resolve()==(B/'NIL_target').resolve()
spec=importlib.util.spec_from_file_location('NIL_private_NHR_stage',B/'NIL_NHR_stage.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
S=B/'NIL_src';O=B/'NIL_extracted';O.mkdir(exist_ok=True)
payload=json.loads(lzma.decompress((P/'NHR_FROZEN_PAYLOAD.json.xz').read_bytes()))
changed=['crates/aspis-r1-cost-probe/src/lib.rs','crates/aspis-r1-cost-probe/src/candidate.rs'];before={n:(S/n).read_bytes() for n in changed}
for n in changed:(S/n).write_bytes(base64.b64decode(payload[n]))
status=1;finding=None
try:
 args=types.SimpleNamespace(function='tx2_common',opacity=str(B/'NIL_EXTRACT_OPACITY.json'),cargo='/home/dombarker/.cargo/bin/cargo')
 status=m.extract(args,S,O)
except Exception as e:
 finding=repr(e);print('NIL extraction finding:',finding,flush=True)
finally:
 for n,raw in before.items():(S/n).write_bytes(raw)
 assert all((S/n).read_bytes()==raw for n,raw in before.items())
 files={}
 for p in sorted(O.rglob('*')):
  if p.is_file():files[str(p.relative_to(O))]=dict(sha256=sha(p),bytes=p.stat().st_size,base64=base64.b64encode(p.read_bytes()).decode())
 raw=json.dumps(files,separators=(',',':')).encode();(B/'NIL_EXTRACT_OUTPUTS.json.xz').write_bytes(lzma.compress(raw,preset=6));(B/'NIL_EXTRACT_OUTPUTS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
 out=dict(status=status,finding=finding,stager_sha256=pins['stager_sha256'],opacity_sha256=pins['opacity_sha256'],source_restored=True,shared_writes=False,reused_workspace=str(S),reused_target=str(B/'NIL_target'),payload_files=len(files),payload_uncompressed_bytes=len(raw),payload_sha256=hashlib.sha256(raw).hexdigest(),NHR_pins=json.loads((O/'NHR_PINS.json').read_text()) if (O/'NHR_PINS.json').exists() else None)
 (B/'NIL_EXTRACTION_PINS.json').write_text(json.dumps(out,indent=2)+'\n')
sys.exit(status)
