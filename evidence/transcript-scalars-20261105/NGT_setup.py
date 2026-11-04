"""Seed private source/cache copies; never alters predecessor trees."""
from pathlib import Path
import subprocess,json,hashlib,lzma
E=Path(__file__).resolve().parent
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
raw=subprocess.check_output(['git','archive',rev,'Cargo.toml','Cargo.lock','crates','programs','docs/research/v8-r0-zk-20261009/c3/build','docs/research/v8-r0-zk-20261009/c3/check'])
p=E/'NGT_FROZEN.tar.xz';p.write_bytes(lzma.compress(raw,preset=6));(E/'NGT_FROZEN.tar.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
(E/'NGT_ARCHIVE_PIN.json').write_text(json.dumps(dict(revision=rev,bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest(),compressed_sha256=hashlib.sha256(p.read_bytes()).hexdigest()),indent=2))
