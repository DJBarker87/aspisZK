from pathlib import Path
import subprocess,os,hashlib,json,tomllib
b=Path(__file__).resolve().parent;s=b/'SDY_src';lock=s/'Cargo.lock'
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pre=h(lock)
cargo='/home/dombarker/.cargo/bin/cargo';env=os.environ.copy();env.update(CARGO_NET_OFFLINE='true',CARGO_TARGET_DIR=str(b/'SDY_target'))
m=subprocess.run([cargo,'metadata','--format-version','1','--locked','--offline','--manifest-path',str(s/'Cargo.toml')],env=env,capture_output=True,text=True)
(b/'SDY_metadata_stderr.log').write_text(m.stderr);assert m.returncode==0,m.stderr
d=json.loads(m.stdout);pins={(p['name'],p['version'],p.get('source')) for p in tomllib.loads(lock.read_text())['package']}
for p in d['packages']:assert (p['name'],p['version'],p.get('source')) in pins,(p['name'],p['version'],p.get('source'))
assert d['resolve'] is not None
(b/'SDY_graph.json').write_text(json.dumps({'metadata_sha256':hashlib.sha256(m.stdout.encode()).hexdigest(),'packages':[(p['name'],p['version'],p.get('source')) for p in d['packages']],'node_count':len(d['resolve']['nodes']),'lock_sha256':pre},indent=2)+'\n')
r=subprocess.run([cargo,'test','--release','--locked','--offline','-j','4','--manifest-path',str(s/'Cargo.toml'),'-p','aspis-r1-cost-probe','--lib','SDY_','--','--nocapture'],env=env)
post=h(lock);(b/'SDY_lock.json').write_text(json.dumps({'before':pre,'after':post,'unchanged':pre==post},indent=2)+'\n');assert post==pre
raise SystemExit(r.returncode)
