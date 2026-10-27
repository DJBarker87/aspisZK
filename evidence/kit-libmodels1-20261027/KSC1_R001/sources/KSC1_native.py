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
m=subprocess.run([str(tool/'cargo'),'metadata','--format-version','1','--locked','--offline','--manifest-path',str(S/'Cargo.toml')],env=env,capture_output=True,text=True)
(B/'KSC1_metadata_stderr.log').write_text(m.stderr);assert m.returncode==0,m.stderr
x=json.loads(m.stdout);pins={(p['name'],p['version'],p.get('source')) for p in tomllib.loads((S/'Cargo.lock').read_text())['package']}
assert all((p['name'],p['version'],p.get('source')) in pins for p in x['packages']);assert x['resolve']
(B/'KSC1_graph.json').write_text(json.dumps(dict(metadata_sha256=hashlib.sha256(m.stdout.encode()).hexdigest(),packages=[(p['name'],p['version'],p.get('source')) for p in x['packages']],nodes=len(x['resolve']['nodes']),lock_sha256=before),indent=2))
# Compile only the std-only scratch diagnostic, with an explicitly optimized profile.
cmd=[str(tool/'rustc'),'--edition=2021','-O','-C','overflow-checks=yes','--test',str(B/'KSC1_native_test.rs'),'-o',str(B/'KSC1_native_test')]
r=subprocess.run(cmd,env=env)
if r.returncode==0:r=subprocess.run([str(B/'KSC1_native_test'),'--nocapture','--test-threads=1'],env=env)
after=sha(S/'Cargo.lock');assert before==after
(B/'KSC1_lock.json').write_text(json.dumps(dict(before=before,after=after,unchanged=before==after,compile_command=cmd,profile='rustc -O, overflow-checks=yes',offline=True)))
print(subprocess.check_output([str(tool/'rustc'),'-vV'],text=True))
raise SystemExit(r.returncode)
