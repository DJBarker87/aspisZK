from pathlib import Path
import subprocess,json,hashlib,os,tomllib
B=Path(__file__).resolve().parent;S=B/'KSC1_scratch';S.mkdir(exist_ok=True)
F=Path('/home/dombarker/project-offloads/codex-cx-assoc-a4-cache-20261027/KSA_src')
# Private scratch root and frozen lock; reuse the frozen read-only source tree via symlinks.
for n in ['Cargo.toml','Cargo.lock']:(S/n).write_bytes((F/n).read_bytes())
for p in F.iterdir():
 if p.is_dir() and not (S/p.name).exists():(S/p.name).symlink_to(p,target_is_directory=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();before=sha(S/'Cargo.lock')
assert before=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
env=os.environ.copy();env['CARGO_NET_OFFLINE']='true'
tool=Path('/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/bin')
env['RUSTC']=str(tool/'rustc')
m=subprocess.run([str(tool/'cargo'),'metadata','--format-version','1','--locked','--offline','--manifest-path',str(S/'Cargo.toml')],env=env,capture_output=True,text=True)
(B/'KSC1_metadata_stderr.log').write_text(m.stderr);assert m.returncode==0,m.stderr
x=json.loads(m.stdout);pins={(p['name'],p['version'],p.get('source')) for p in tomllib.loads((S/'Cargo.lock').read_text())['package']}
assert all((p['name'],p['version'],p.get('source')) in pins for p in x['packages']);assert x['resolve']
# Also pin every frozen manifest and validate resolved graph edges against the lock.
mf=json.loads((B/'KSC1_frozen_manifest.json').read_text())
for p in mf['files']:
 if p['path'].endswith('Cargo.toml'):
  assert sha(F/p['path'])==p['sha256'],p['path']
byid={p['id']:p for p in x['packages']}
locked={(p['name'],p['version'],p.get('source')):p for p in tomllib.loads((S/'Cargo.lock').read_text())['package']}
edges=[]
for node in x['resolve']['nodes']:
 p=byid[node['id']];key=(p['name'],p['version'],p.get('source'));declared=locked[key].get('dependencies',[])
 for depid in node['dependencies']:
  q=byid[depid];matches=[entry for entry in declared if entry.split()[0]==q['name'] and (len(entry.split())==1 or entry.split()[1]==q['version'])]
  assert matches,(key,q)
  edges.append([list(key),[q['name'],q['version'],q.get('source')]])
(B/'KSC1_graph_edges.json').write_text(json.dumps(dict(edges=edges,manifest_sha256=sha(B/'KSC1_frozen_manifest.json'),all_frozen_manifests_match=True),indent=2))
(B/'KSC1_graph.json').write_text(json.dumps(dict(metadata_sha256=hashlib.sha256(m.stdout.encode()).hexdigest(),packages=[(p['name'],p['version'],p.get('source')) for p in x['packages']],nodes=len(x['resolve']['nodes']),lock_sha256=before),indent=2))
# Compile only the std-only scratch diagnostic, with an explicitly optimized profile.
cmd=[str(tool/'rustc'),'--edition=2021','-O','-C','overflow-checks=yes','--test',str(B/'KSC1_native_test.rs'),'-o',str(B/'KSC1_native_test')]
r=subprocess.run(cmd,env=env)
if r.returncode==0:r=subprocess.run([str(B/'KSC1_native_test'),'--nocapture','--test-threads=1'],env=env)
after=sha(S/'Cargo.lock');assert before==after
(B/'KSC1_lock.json').write_text(json.dumps(dict(before=before,after=after,unchanged=before==after,compile_command=cmd,profile='rustc -O, overflow-checks=yes',offline=True)))
print(subprocess.check_output([str(tool/'rustc'),'-vV'],text=True))
raise SystemExit(r.returncode)
