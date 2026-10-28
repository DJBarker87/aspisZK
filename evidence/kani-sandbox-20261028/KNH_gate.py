"""Strict read-only frozen graph preflight, then standalone scratch Kani."""
from pathlib import Path
import json,hashlib,subprocess,sys,os,tomllib
b=Path(__file__).resolve().parent;a=sys.argv[1]
# Reuse the existing retained frozen metadata workspace; never compile into it.
s=Path('/home/dombarker/project-offloads/codex-cx-kani-mitig-20261028/KMX_src')
lock=s/'Cargo.lock';expected='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
assert hashlib.sha256(lock.read_bytes()).hexdigest()==expected
metaenv=os.environ.copy();metaenv.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_TARGET_DIR=str(b/'KNH_metadata_target'),CARGO_NET_OFFLINE='true');metaenv.pop('RUSTUP_HOME',None);metaenv.pop('RUSTUP_TOOLCHAIN',None)
r=subprocess.run(['/home/dombarker/.cargo/bin/cargo','metadata','--manifest-path',str(s/'Cargo.toml'),'--locked','--offline','--format-version','1'],capture_output=True,text=True,env=metaenv)
(b/(a+'-metadata.stderr')).write_text(r.stderr);assert r.returncode==0,r.stderr
# Some wrappers prefix diagnostics: consume JSON from its first opening brace.
pos=r.stdout.find('{');m=json.loads(r.stdout[pos:]);(b/(a+'-metadata.json')).write_text(json.dumps(m))
key=lambda p:json.dumps([p['name'],p['version'],p.get('source')],separators=(',',':'))
keys={p['id']:key(p) for p in m['packages']}
graph={'packages':sorted(keys.values()),'edges':sorted([keys[n['id']],sorted(keys[d] for d in n['dependencies'])] for n in m['resolve']['nodes'])}
reference=json.loads((b/'KNH_frozen_graph.json').read_text());assert graph==reference,'STOP: frozen graph mismatch'
features={keys[n['id']]:n['features'] for n in m['resolve']['nodes']}
out=dict(exact_frozen_graph_match=True,metadata_workspace=str(s),metadata_read_only=True,graph_sha256=hashlib.sha256(json.dumps(graph,sort_keys=True).encode()).hexdigest(),lock_before=expected,resolved_features=features,standalone_external_dependencies=[])
p=b/(a+'-strict-graph.json');p.write_text(json.dumps(out,indent=2)+'\n')
print('KNH_STRICT_GRAPH_MATCH',flush=True)
r=subprocess.run(sys.argv[2:],env=os.environ)
out.update(lock_after=hashlib.sha256(lock.read_bytes()).hexdigest(),scratch_lock_after=hashlib.sha256((b/'KNH_scratch/Cargo.lock').read_bytes()).hexdigest(),kani_exit=r.returncode)
p.write_text(json.dumps(out,indent=2)+'\n');assert out['lock_after']==out['scratch_lock_after']==expected,'STOP lock drift'
sys.exit(r.returncode)
