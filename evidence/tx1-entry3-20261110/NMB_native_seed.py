from NMB_formal import *
import base64
P=E.parent/'sdk-borrow-20261109/NLF_FROZEN_INPUTS.json.xz'
raw=lzma.decompress(P.read_bytes());frozen=json.loads(raw)
files={n.replace('NLF_src/','NMB_src/').replace('NLF_FROZEN_PINS','NMB_FROZEN_PINS').replace('NLF_KMX','NMB_KMX'):v for n,v in frozen.items()}
script="""from pathlib import Path
import json,shutil,base64,lzma,hashlib,subprocess
b=Path(__file__).resolve().parent;s=b/'NMB_src';assert not s.exists()
shutil.copytree('/home/dombarker/project-offloads/codex-cx-sdk-borrow-20261109/NLF_src',s,ignore=shutil.ignore_patterns('target','.git','__pycache__'))
f=json.loads(lzma.decompress(base64.b64decode(PAYLOAD)))
for n,t in f.items():
 p=b/n;p.parent.mkdir(parents=True,exist_ok=True)
 p.write_bytes(base64.b64decode(t)) if n.startswith('NMB_src/') else p.write_text(t)
# Existing mitigation files must already have the exact admitted content.
expect={'KMX_stubs.rs':'ad8efb63d8ff791274c91eff9ccc5b9fb126f5a3ac7f27aa811ca11b8e25c138','KMX_native.rs':'cf719c47b5c8c91dcc369984c01bd0b8531b25210e344c9fd06db21b30171880','KMX_CopyMeaning.lean':'2baec49a3446a3bbb2be6f992c97d0a6897534a1cd308db8746194dedf665f2b'}
for n,h in expect.items():assert hashlib.sha256((s/n).read_bytes()).hexdigest()==h
pins=json.loads((b/'NMB_FROZEN_PINS.json').read_text());assert all(hashlib.sha256((s/n).read_bytes()).hexdigest()==h for n,h in pins.items())
size=sum(p.stat().st_size for p in s.rglob('*') if p.is_file());assert size<30_000_000_000
print(json.dumps(dict(frozen_files=len(pins),bytes=size,source_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',kmx_patch_sha256=hashlib.sha256((b/'NMB_KMX_copy_stubs.patch').read_bytes()).hexdigest(),lock_sha256=hashlib.sha256((s/'Cargo.lock').read_bytes()).hexdigest(),CARGO_TARGET_DIR=str(b/'NMB_target'))))
""".replace('PAYLOAD',repr(base64.b64encode(lzma.compress(json.dumps(files).encode())).decode()))
(E/'NMB_NATIVE_INPUT_PIN.json').write_text(json.dumps(dict(path=str(P.relative_to(E.parent.parent)),sha256=sha(raw),archive_sha256=sha(P.read_bytes())),indent=2)+'\n')
r=run('NMB_L010','inspect','NMB_native_seed',command=['python3','NMB_native_seed_host.py'],extra={'NMB_native_seed_host.py':script})
assert r['exit_status']==0
