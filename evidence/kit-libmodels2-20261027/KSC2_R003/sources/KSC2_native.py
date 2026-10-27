from pathlib import Path
import subprocess,os,json,hashlib,shutil,tomllib
B=Path(__file__).resolve().parent
S=B/'KSC2_scratch'; K=Path('/home/dombarker/project-offloads/codex-cx-assoc-a4-cache-20261027/KSA_src')
S.mkdir(exist_ok=True)
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
# A manifest-only scratch tree, not a second source corpus. No shipped body is needed
# for a std-only test. Every Cargo manifest and the release lock remain byte-identical.
manifest=[]
for p in K.rglob('Cargo.toml'):
 if 'target' in p.parts:continue
 dest=S/p.relative_to(K);dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,dest)
 manifest.append(dict(path=str(p.relative_to(K)),sha256=h(p)))
 d=tomllib.loads(p.read_text())
 if 'package' in d:
  for rel in ['src/lib.rs','src/main.rs']+[t.get('path','src/lib.rs') for typ in ['lib','bin','example','test','bench'] for t in ([d[typ]] if isinstance(d.get(typ),dict) else d.get(typ,[]))]:
   stub=dest.parent/rel;stub.parent.mkdir(parents=True,exist_ok=True);stub.write_text('fn main() {}\n')
lock=S/'Cargo.lock'
if not lock.exists():shutil.copyfile(K/'Cargo.lock',lock)
pre=h(lock);assert pre=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
env=os.environ.copy();env['CARGO_NET_OFFLINE']='true'
cargo='/home/dombarker/.cargo/bin/cargo';rustc='/home/dombarker/.cargo/bin/rustc'
version=subprocess.check_output([rustc,'-Vv'],text=True);assert 'rustc 1.94.1 (e408947bf' in version
m=subprocess.run([cargo,'metadata','--format-version','1','--locked','--offline','--manifest-path',str(S/'Cargo.toml')],env=env,capture_output=True,text=True)
(B/'KSC2_metadata_stderr.log').write_text(m.stderr)
assert m.returncode==0,m.stderr
d=json.loads(m.stdout);pins={(p['name'],p['version'],p.get('source')) for p in tomllib.loads(lock.read_text())['package']}
for p in d['packages']:assert (p['name'],p['version'],p.get('source')) in pins,p['name']
assert d['resolve'] is not None
(B/'KSC2_graph.json').write_text(json.dumps(dict(metadata_sha256=hashlib.sha256(m.stdout.encode()).hexdigest(),packages=[(p['name'],p['version'],p.get('source')) for p in d['packages']],nodes=len(d['resolve']['nodes']),lock_sha256=pre,manifests=manifest,rustc=version),indent=2)+'\n')
cmd=[rustc,'--edition=2021','--test','-C','opt-level=3','-C','overflow-checks=yes',str(B/'KSC2_native_test.rs'),'-o',str(B/'KSC2_std_tests')]
print('OPTIMIZED STD-ONLY DIFFERENTIAL',cmd,flush=True)
r=subprocess.run(cmd,env=env)
if r.returncode==0:r=subprocess.run([str(B/'KSC2_std_tests'),'KSC2::additional_branches','--nocapture','--test-threads=1'],env=env)
post=h(lock);(B/'KSC2_lock.json').write_text(json.dumps(dict(before=pre,after=post,unchanged=pre==post,compilation='rustc --test -C opt-level=3 -C overflow-checks=yes; no Cargo compilation or release source linkage'))+'\n');assert pre==post
raise SystemExit(r.returncode)
