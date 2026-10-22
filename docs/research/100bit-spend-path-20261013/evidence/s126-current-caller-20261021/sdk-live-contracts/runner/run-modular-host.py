#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,os,subprocess,sys,tomllib
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');name,crate,harness=sys.argv[1:4];crate=Path(crate)
os.environ.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_BUILD_JOBS='1',CARGO_NET_OFFLINE='true',CARGO_TARGET_DIR=str(H/'target'),RUSTFLAGS='-C opt-level=3 -C overflow-checks=yes -C link-arg=-Wl,--threads=1')
subprocess.run(['python3',str(H/'kit/reservation.py'),str(H/(name+'-admission.json'))],check=True,stdout=subprocess.DEVNULL)
cmd=['cargo','kani','--manifest-path',str(crate/'Cargo.toml'),'--lib','--exact','--harness',harness,'--solver','cadical','--no-assertion-reach-checks','-j','1','-Z','unstable-options','--output-format','terse','--harness-timeout','600','--cbmc-args','--unwinding-assertions']
if len(sys.argv)>4 and sys.argv[4] in ['codegen','codegen-stubbing','codegen-contracts-stubbing']:
 pos=cmd.index('--cbmc-args');cmd[pos:pos]=['--only-codegen']
if len(sys.argv)>4 and sys.argv[4] in ['contracts','contracts-stubbing','codegen-contracts-stubbing']:
 pos=cmd.index('--cbmc-args');cmd[pos:pos]=['-Z','function-contracts']
if len(sys.argv)>4 and sys.argv[4] in ['stubbing','codegen-stubbing','contracts-stubbing','codegen-contracts-stubbing']:
 pos=cmd.index('--cbmc-args');cmd[pos:pos]=['-Z','stubbing']
if len(sys.argv)>5 and sys.argv[5]=='verbose':cmd.insert(2,'--verbose')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
patched={}
for package,settings in tomllib.loads((crate/'Cargo.toml').read_text()).get('patch',{}).get('crates-io',{}).items():
 if 'path' not in settings:continue
 root=Path(settings['path']);root=root if root.is_absolute() else crate/root
 patched[package]=dict(root=str(root),files={str(p.relative_to(root)):sha(p) for p in root.rglob('*') if p.is_file() and (p.suffix in ['.rs','.toml','.json'] or p.name=='Cargo.lock')})
(H/(name+'-input.json')).write_text(json.dumps(dict(command=cmd,runner_sha256=sha(Path(__file__)),patched_source_pins=patched,crate_source_pins={str(p.relative_to(crate)):sha(p) for p in (crate/'src').rglob('*.rs')},cargo_lock_sha256=sha(crate/'Cargo.lock') if (crate/'Cargo.lock').is_file() else None,source_sha256=sha(crate/'src/lib.rs'),cargo_sha256=sha(crate/'Cargo.toml'),tool_pins={str(p):sha(p) for p in Path('/home/dombarker/.kani/kani-0.67.0/bin').iterdir() if p.is_file()},env={n:os.environ[n] for n in ['RUSTFLAGS','CARGO_BUILD_JOBS','CARGO_TARGET_DIR','CARGO_NET_OFFLINE']},expected_time='Optimized cached compilation, then named actual SDK guard/prefix certificate; assertion checks and unwinding assertions enabled, per-assertion reachability queries omitted.'),indent=2)+'\n')
os.chdir(crate)
raise SystemExit(subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(H/'kit/capped.py'),str(H/'receipts'/name),('Parametric original from_fn control, total-pure multiplication contract; no arithmetic evaluation' if 'powers' in name else 'Actual SDK modular guard/prefix check: cached optimized compilation then CBMC'),'--',*cmd]))
