"""Final retained workspace/disk/lock evidence; no build or source mutation."""
from pathlib import Path
import json,hashlib,os,shutil
B=Path.cwd();assert str(B)=='/home/dombarker/project-offloads/codex-cx-tx1-finish-20261110'
size=0;files=0
for root,dirs,names in os.walk(B,followlinks=False):
 for name in names:
  p=Path(root)/name
  if not p.is_symlink():size+=p.stat().st_size;files+=1
lock=B/'NLI_src/Cargo.lock';h=hashlib.sha256(lock.read_bytes()).hexdigest()
a=dict(workspace=str(B),cargo_target_dir=os.environ['CARGO_TARGET_DIR'],tmpdir=os.environ['TMPDIR'],retained=True,owned_bytes=size,files=files,disk=shutil.disk_usage(B)._asdict(),lock_sha256=h,scope='Final read-only retained-workspace/disk/lock receipt; prelaunch-only L009 slot reused after preserving its original input evidence')
assert size<30_000_000_000
assert a['cargo_target_dir']==str(B/'NLI_target')
assert a['tmpdir']==str(B/'NLI_tmp')
assert h=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
(B/'NLI_HOST_FINAL.json').write_text(json.dumps(a,indent=2)+'\n')
print(json.dumps(dict(owned_bytes=size,retained=True,lock_unchanged=True)))
