"""Validate selected SDK source against frozen lock archives, preserving bytes."""
from pathlib import Path
import hashlib,json,subprocess,tomllib,tarfile,io
E=Path(__file__).resolve().parent
registry=Path('/Users/dominic/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f')
lock=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:Cargo.lock'])
packages=tomllib.loads(lock.decode())['package'];records=[]
selected=[('solana-program-entrypoint','2.3.0','lib.rs'),('solana-program-error','2.2.2','lib.rs'),('solana-instruction',None,'error.rs'),('solana-program','2.3.0','program.rs'),('solana-cpi','2.2.1','lib.rs')]
for name,version,filename in selected:
 package=next(p for p in packages if p['name']==name and (version is None or p['version']==version))
 stem=name+'-'+package['version'];source=registry/stem/'src'/filename
 archive=registry.parent.parent/'cache'/registry.name/(stem+'.crate');raw=source.read_bytes();arc=archive.read_bytes()
 assert hashlib.sha256(arc).hexdigest()==package['checksum']
 with tarfile.open(fileobj=io.BytesIO(arc)) as t:assert t.extractfile(stem+'/src/'+filename).read()==raw
 dest=E/('PCC_'+stem+'_'+filename+'.txt')
 if dest.exists():assert dest.read_bytes()==raw
 else:dest.write_bytes(raw)
 records.append(dict(package=package,source=str(dest.relative_to(E)),sha256=hashlib.sha256(raw).hexdigest(),archive_sha256=hashlib.sha256(arc).hexdigest(),archive_matches_lock=True,source_matches_archive=True))
(E/'PCC_SDK_PINS.json').write_text(json.dumps(dict(frozen_lock_sha256=hashlib.sha256(lock).hexdigest(),packages=records),indent=1)+'\n')
print('Five SDK sources match frozen lock archives byte-for-byte')
