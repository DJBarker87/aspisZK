import pathlib,subprocess,os,hashlib,json,tomllib
b=pathlib.Path(__file__).resolve().parent;s=b/'SDX_src';lock=s/'Cargo.lock'
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
source=s/'crates/aspis-r1-cost-probe/src/sampler.rs'
source.write_bytes(source.read_bytes().split(b'\n#[cfg(test)]\nmod SDX_diagnostic')[0])
pre=h(lock); original=h(source)
with (s/'crates/aspis-r1-cost-probe/src/sampler.rs').open('a') as f:f.write((b/'SDX_native_test.rs').read_text())
cargo='/home/dombarker/.cargo/bin/cargo'
env=os.environ.copy();env['CARGO_NET_OFFLINE']='true';env['CARGO_TARGET_DIR']=str(b/'SDX_target')
m=subprocess.run([cargo,'metadata','--format-version','1','--locked','--offline','--manifest-path',str(s/'Cargo.toml')],env=env,capture_output=True,text=True)
(b/'SDX_metadata_stderr.log').write_text(m.stderr);assert m.returncode==0,m.stderr
d=json.loads(m.stdout);locked=tomllib.loads(lock.read_text()); pins={(p['name'],p['version'],p.get('source')) for p in locked['package']}
for p in d['packages']:
 assert (p['name'],p['version'],p.get('source')) in pins,(p['name'],p['version'],p.get('source'))
assert d['resolve'] is not None
(b/'SDX_graph.json').write_text(json.dumps({'metadata_sha256':hashlib.sha256(m.stdout.encode()).hexdigest(),'packages':[(p['name'],p['version'],p.get('source')) for p in d['packages']],'node_count':len(d['resolve']['nodes']),'lock_sha256':pre,'sampler_original_sha256':original},indent=2)+'\n')
r=subprocess.run([cargo,'test','--release','--locked','--offline','-j','4','--manifest-path',str(s/'Cargo.toml'),'-p','aspis-r1-cost-probe','--lib','SDX_four_blocks','--','--nocapture'],env=env)
post=h(lock);(b/'SDX_lock.json').write_text(json.dumps({'before':pre,'after':post,'unchanged':pre==post},indent=2)+'\n');assert post==pre
raise SystemExit(r.returncode)
