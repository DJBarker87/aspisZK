"""Own wrapper: repair own target link, restore ALL staged frozen bytes, preflight, extract once, restore harness bytes."""
from pathlib import Path
import sys,importlib.util,hashlib,json,types,lzma,base64,os
sys.dont_write_bytecode=True
B=Path(__file__).resolve().parent;P=B.parent/'codex-cx-extract-stage-20261106'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins=json.loads((B/'NIY_EXTRACT_INPUT_PINS.json').read_text())
assert sha(B/'NIY_NHR_stage.py')==sha(P/'NHR_stage.py')==pins['stager_sha256']
assert sha(B/'NIY_EXTRACT_OPACITY.json')==pins['opacity_sha256']
for name in ['NHR_STAGING_MANIFEST.json','NHR_FROZEN_PAYLOAD.json.xz','NHR_FROZEN_PAYLOAD.json.sha256']:
 link=B/name
 if not link.exists() and not link.is_symlink():link.symlink_to(P/name)
 assert link.resolve()==(P/name).resolve()
(B/'NIY_target').mkdir(exist_ok=True)
link=B/'NHR_target'
if not link.exists() and not link.is_symlink():link.symlink_to(B/'NIY_target',target_is_directory=True)
assert link.is_dir() and link.resolve()==(B/'NIY_target').resolve(),'own target link must resolve before Charon'
spec=importlib.util.spec_from_file_location('NIY_private_NHR_stage',B/'NIY_NHR_stage.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
S=B/'NIY_src';preflight='--preflight' in sys.argv;O=B/('NIY_preflight' if preflight else 'NIY_extracted');O.mkdir(exist_ok=True)
payload=json.loads(lzma.decompress((P/'NHR_FROZEN_PAYLOAD.json.xz').read_bytes()))
changed={n:(S/n).read_bytes() for n,raw in payload.items() if (S/n).read_bytes()!=base64.b64decode(raw)}
for n in changed:(S/n).write_bytes(base64.b64decode(payload[n]))
status=1;finding=None
try:
 args=types.SimpleNamespace(function='tx2_common',opacity=str(B/'NIY_EXTRACT_OPACITY.json'),cargo='/home/dombarker/.cargo/bin/cargo')
 os.environ.update(CARGO_PROFILE_DEV_OPT_LEVEL='3',CARGO_PROFILE_DEV_DEBUG='0',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true')
 m.validate(S,O,args.cargo)
 if preflight:status=0
 else:status=m.extract(args,S,O)
except Exception as e:
 finding=repr(e);print('NIY extraction/preflight finding:',finding,flush=True)
finally:
 for n,raw in changed.items():(S/n).write_bytes(raw)
 assert all((S/n).read_bytes()==raw for n,raw in changed.items())
 files={}
 for p in sorted(O.rglob('*')):
  if p.is_file():files[str(p.relative_to(O))]=dict(sha256=sha(p),bytes=p.stat().st_size,base64=base64.b64encode(p.read_bytes()).decode())
 raw=json.dumps(files,separators=(',',':')).encode();stem='NIY_PREFLIGHT' if preflight else 'NIY_EXTRACT'
 (B/(stem+'_OUTPUTS.json.xz')).write_bytes(lzma.compress(raw,preset=6));(B/(stem+'_OUTPUTS.json.sha256')).write_text(hashlib.sha256(raw).hexdigest()+'\n')
 out=dict(status=status,finding=finding,preflight=preflight,stager_sha256=pins['stager_sha256'],opacity_sha256=pins['opacity_sha256'],own_target_link=str(link),target_resolves=link.is_dir(),source_restored=True,restored_files=sorted(changed),shared_writes=False,reused_workspace=str(S),CARGO_TARGET_DIR=str(B/'NIY_target'),payload_files=len(files),payload_uncompressed_bytes=len(raw),payload_sha256=hashlib.sha256(raw).hexdigest(),NHR_pins=json.loads((O/'NHR_PINS.json').read_text()) if (O/'NHR_PINS.json').exists() else None)
 (B/(stem+'_PINS.json')).write_text(json.dumps(out,indent=2)+'\n')
sys.exit(status)
