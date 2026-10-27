from pathlib import Path
import subprocess,os,json,hashlib,tomllib
B=Path(__file__).resolve().parent;S=B/'KSA_src';lock=S/'Cargo.lock'
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pre=h(lock);env=os.environ.copy();env.update(CARGO_NET_OFFLINE='true',CARGO_TARGET_DIR=str(B/'KSA_target'),CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true')
cargo='/home/dombarker/.cargo/bin/cargo'
m=subprocess.run([cargo,'metadata','--format-version','1','--locked','--offline','--manifest-path',str(S/'Cargo.toml')],env=env,capture_output=True,text=True)
(B/'KSA_metadata_stderr.log').write_text(m.stderr)
if m.returncode:raise SystemExit(m.returncode)
d=json.loads(m.stdout);pins={(p['name'],p['version'],p.get('source')) for p in tomllib.loads(lock.read_text())['package']}
for p in d['packages']:assert (p['name'],p['version'],p.get('source')) in pins,p['name']
assert d['resolve'] is not None
(B/'KSA_graph.json').write_text(json.dumps(dict(metadata_sha256=hashlib.sha256(m.stdout.encode()).hexdigest(),packages=[(p['name'],p['version'],p.get('source')) for p in d['packages']],nodes=len(d['resolve']['nodes']),lock_sha256=pre),indent=2)+'\n')
r=subprocess.run([cargo,'test','--release','--locked','--offline','-j','4','--manifest-path',str(S/'Cargo.toml'),'-p','aspis-core','--lib','KSA_frozen_differential','--','--nocapture'],env=env)
post=h(lock);(B/'KSA_lock.json').write_text(json.dumps(dict(before=pre,after=post,unchanged=pre==post))+'\n');assert pre==post
raise SystemExit(r.returncode)
