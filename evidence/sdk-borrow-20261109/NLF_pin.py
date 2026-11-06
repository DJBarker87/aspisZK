from NLF_transport import *
import hashlib,lzma,base64,tomllib
sha=lambda b:hashlib.sha256(b).hexdigest()
frozen='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
lock=subprocess.check_output(['git','show',frozen+':Cargo.lock']);l=tomllib.loads(lock.decode())
wanted=['solana-program','solana-account-info','solana-program-error']
packages=[p for p in l['package'] if p['name'] in wanted]
r=ssh('python3',f'''from pathlib import Path
import json,hashlib,base64,lzma
roots=[Path('/home/dombarker/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f')]
paths=[roots[0]/(p['name']+'-'+p['version'])/'src/lib.rs' for p in {packages!r}]
paths += [Path('/home/dombarker/.rustup/toolchains/1.89.0-sbpf-solana-v1.52/lib/rustlib/src/rust/library/core/src/cell.rs'),Path('/home/dombarker/.kani/kani-0.67.0/rustc-version')]
rows=[]
for p in paths:
 raw=p.read_bytes();rows.append(dict(path=str(p),sha256=hashlib.sha256(raw).hexdigest(),bytes=len(raw),data=base64.b64encode(lzma.compress(raw)).decode()))
print(json.dumps(rows))
''');assert r.returncode==0,r.stderr
rows=json.loads(r.stdout);(E/'NLF_PINNED_INPUTS').mkdir(exist_ok=True)
for x in rows:
 raw=base64.b64decode(x.pop('data'));p=E/'NLF_PINNED_INPUTS'/(x['sha256']+'.xz');p.write_bytes(raw);x['archive']=str(p.relative_to(E));x['archive_sha256']=sha(raw)
(E/'NLF_SDK_PINS.json').write_text(json.dumps(dict(frozen_revision=frozen,lock_sha256=sha(lock),packages=packages,sources=rows,core_source_scope='deployed 1.89.0-sbpf-solana-v1.52; Kani backend is separately pinned at rustc 1.93.0-nightly (53732d5e0 2025-11-20); std semantics interpreted under (be)/(au), no equality of compiler versions asserted',CARGO_TARGET_DIR=B+'/NLF_target'),indent=1)+'\n')
print('NLF SDK/core sources pinned and archived once by sha256')
