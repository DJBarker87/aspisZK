"""Owned byte-for-byte NFY seed, including its canonical priority exports."""
from pathlib import Path
import shutil,json,hashlib,lzma
P=Path('/home/dombarker/project-offloads');C=P/'codex-cx-slice-s-retarget2-cache-20261104';B=P/'codex-cx-slice-s-retarget2-20261104';S=P/'codex-cx-slice-s-retarget-cache-20261104';W=P/'codex-cx-sound-int2-20261025'
ad=json.loads((B/'NGE_SEED_ADMISSION.json').read_text());assert ad['allowed'] is True
C.mkdir(exist_ok=True);pins=[]
for src in sorted(S.rglob('*')):
 if not src.is_file():continue
 rel=src.relative_to(S);dst=C/rel;dst.parent.mkdir(parents=True,exist_ok=True)
 if dst.exists():assert dst.read_bytes()==src.read_bytes()
 else:shutil.copy2(src,dst)
 pins.append(dict(source=str(src),destination=str(dst),bytes=dst.stat().st_size,sha256=hashlib.sha256(dst.read_bytes()).hexdigest()))
raw=json.dumps(dict(source=str(S),selected=pins),sort_keys=True).encode();(B/'NGE_CACHE_IMPORTS.json.xz').write_bytes(lzma.compress(raw,preset=6));(B/'NGE_CACHE_IMPORTS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
for n in ['S2W_run_host.py','S2W_lean_host.py','lakefile.toml','lake-manifest.json','lean-toolchain']:shutil.copy2(W/n,B/n)
print(json.dumps(dict(files=len(pins),bytes=sum(p['bytes'] for p in pins),manifest_sha256=hashlib.sha256(raw).hexdigest())))
