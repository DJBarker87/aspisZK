from NJN_transport import *
import hashlib,lzma
r=ssh('python3', '''from pathlib import Path
import json
r=Path('/home/dombarker/.cargo/registry/src/index.crates.io-6f17d22bba15001f')
names=['solana-account-info-2.3.0/src/lib.rs','solana-clock-2.2.3/src/sysvar.rs','solana-pubkey-2.4.0/src/lib.rs','solana-program-error-2.2.2/src/lib.rs','solana-sysvar-2.3.0/src/lib.rs']
print(json.dumps({n:(r/n).read_text() for n in names}))
''')
assert r.returncode==0,r.stderr
x=json.loads(r.stdout);idx={}
for n,t in x.items():
 raw=t.encode();h=hashlib.sha256(raw).hexdigest();p=E/'NJN_SDK_INPUTS'/(h+'.xz');p.parent.mkdir(exist_ok=True);p.write_bytes(lzma.compress(raw));idx[n]=dict(sha256=h,bytes=len(raw),archive=str(p.relative_to(E)))
(E/'NJN_SDK_PINS.json').write_text(json.dumps(idx,indent=1)+'\n')
t=x['solana-pubkey-2.4.0/src/lib.rs'];i=t.index('pub fn create_program_address');print(t[i:i+2600])
