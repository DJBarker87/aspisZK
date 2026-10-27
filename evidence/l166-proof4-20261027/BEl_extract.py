"""Task driver using the existing host reservation and receipt runner unchanged."""
from pathlib import Path
import json,subprocess,sys,time
P=Path(__file__).resolve().parent; R=P.parents[1]
B='/home/dombarker/project-offloads/codex-cx-sound-int2-20261025'; H='dombarker@100.108.41.90'
def ssh(c,**kw):return subprocess.run(['ssh',H,c],**kw)
n=1; harness='charon_body'
rust=False
a='BEl_C01'; assert not (P/a).exists()
if False:

 assert sum(json.loads(x.read_text())['kind']=='kani' for x in P.glob('BEl_K??/receipt.json'))<20
sources=[str(p.relative_to(P)) for p in (P/'BEl_rust').rglob('*') if p.is_file() and p.suffix in ('.rs','.toml','.lock')]
inspection=False
cmd=['/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon','cargo','--preset','aeneas','--mir','built','--sysroot','default','--opaque','crate','--include','crate::BEl_extract','--start-from','crate::BEl_extract::extracted_shipped','--start-from','crate::BEl_extract::extracted_reference','--dest-file',B+'/BEl_Body.llbc','--','--manifest-path',B+'/BEl_rust/Cargo.toml','--offline','--release','--lib','--jobs','1']
cfg=dict(kind='charon',attempt=a,command=cmd,sources=sources,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,timeout=180,expected_time=('optimized Rust compilation then four local non-vacuity fixtures; no elimination' if rust else 'optimized Charon compilation then extract both generic explicit-recorder batch bodies; no stubs'),env=dict(PATH='/home/dombarker/.cargo/bin:/usr/local/bin:/usr/bin:/bin',CARGO_BUILD_JOBS='1',CARGO_PROFILE_DEV_OPT_LEVEL='3',CARGO_PROFILE_DEV_DEBUG='0',CARGO_NET_OFFLINE='true',CARGO_TARGET_DIR=B+'/BEl_target',RUSTFLAGS='--cfg BEl_extract -C opt-level=3 -C link-arg=-Wl,--threads=1',RUSTUP_TOOLCHAIN='nightly-2026-06-01'),deps_fingerprint=dict(scope='self-contained exact source cuts; no Rust dependencies'))
(P/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
retries=[]
for retry in range(11):
 r=ssh(f'python3 /home/dombarker/project-offloads/codex-cx-s2c-20261023/reservation.py {B}/{a}-reservation.json > {B}/{a}-barrier.log 2>&1')
 out=ssh(f'cat {B}/{a}-barrier.log',capture_output=True,text=True); (P/(a+'-barrier.log')).write_text(out.stdout+out.stderr)
 exists=ssh(f'test -f {B}/{a}-reservation.json').returncode==0
 if r.returncode==0 and exists:break
 if r.returncode==78 and retry<10:retries.append(dict(wait_seconds=180,reason='contention'));print('Reservation contention; waiting180s',flush=True);time.sleep(180);continue
 if (not exists or 'FileNotFoundError' in out.stdout) and retry==0:retries.append(dict(wait_seconds=30,reason='transient'));time.sleep(30);continue
 print(out.stdout+out.stderr);sys.exit(r.returncode or 1)
ssh(f'mkdir -p {B}/BEl_rust/src')
for f in sources:subprocess.run(['scp','-q',str(P/f),H+':'+B+'/'+f],check=True)
subprocess.run(['scp','-q',str(P/(a+'.json')),H+':'+B+'/'],check=True)
r=ssh(f'cd {B} && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py {a}.json',capture_output=True,text=True)
(P/(a+'-launch.log')).write_text(r.stdout+r.stderr);print(r.stdout+r.stderr)
subprocess.run(['scp','-qr',H+':'+B+'/'+a,str(P)],check=True)
subprocess.run(['scp','-q',H+':'+B+'/'+a+'-reservation.json',str(P)],check=True)
(P/(a+'-retries.json')).write_text(json.dumps(retries,indent=2)+'\n')
sys.exit(r.returncode)
