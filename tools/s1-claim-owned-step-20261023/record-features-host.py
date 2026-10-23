#!/usr/bin/env python3
"""One capped, locked Cargo metadata query; no compilation or proof replay."""
from pathlib import Path
import hashlib,json,os,subprocess
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021')
P=H/'aspis-s1-claim-owned-step-v6'
tag='s1-owned-step-features-v6'
os.environ.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',RUSTFLAGS='',CARGO_NET_OFFLINE='true')
subprocess.run(['python3',str(H/'kit/reservation.py'),str(H/(tag+'-admission.json'))],check=True,stdout=subprocess.DEVNULL)
cmd=['cargo','metadata','--manifest-path',str(P/'Cargo.toml'),'--offline','--locked','--format-version','1']
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
before=sha(P/'Cargo.lock')
status=subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=1G','-p','MemoryMax=2G','-p','MemorySwapMax=0','-p','TasksMax=32','python3',str(H/'kit/capped.py'),str(H/'receipts'/tag),'Locked feature metadata only; no source compilation or verification','--',*cmd])
assert status==0 and sha(P/'Cargo.lock')==before
meta=json.loads((H/'receipts'/tag/'stdout.log').read_text())
byid={p['id']:p for p in meta['packages']}
cargo=Path(subprocess.check_output(['rustup','which','cargo'],text=True).strip())
(H/(tag+'-features.json')).write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',
    command=cmd,cargo_sha256=sha(cargo),cargo_version=subprocess.check_output([str(cargo),'--version','--verbose'],text=True),
    lock_sha256=before,lock_unchanged=True,features=[dict(package=byid[n['id']]['name'],version=byid[n['id']]['version'],manifest=byid[n['id']]['manifest_path'],features=n['features']) for n in meta['resolve']['nodes']]),indent=2)+'\n')
