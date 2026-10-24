#!/usr/bin/env python3
from pathlib import Path
import os,json,subprocess,sys,hashlib
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021')
W=H/'s1-y1-native-v4-20261024';name=sys.argv[1]
assert name in ['shipped_y1_owned_equivalent']
receipt=W/(name+'-receipt');assert not receipt.exists()
subprocess.run(['python3',str(H/'kit/reservation.py'),str(W/(name+'-admission.json'))],check=True,stdout=subprocess.DEVNULL)
snap=subprocess.check_output(['python3','/home/dombarker/project-offloads/r1-circle-sample-wrapper-extraction-v2/collect-cgroups.py'],text=True)
(W/(name+'-global-admission.json')).write_text(snap);ad=json.loads(snap);G=2**30
assert ad['effective_sum_bytes']+8*G<=48*G and ad['MemAvailable_kB']*1024>=14*G,'fresh global admission refused'
os.environ.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_BUILD_JOBS='1',CARGO_NET_OFFLINE='true',CARGO_TARGET_DIR=str(W/'target'),RUSTFLAGS='-C opt-level=3 -C overflow-checks=yes -C link-arg=-Wl,--threads=1')
for n in ['RUSTUP_TOOLCHAIN','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_ENCODED_RUSTFLAGS']:os.environ.pop(n,None)
os.chdir(W)
cmd=['cargo','kani','--lib','--exact','--harness','proofs::'+name,'-j','1','-Z','unstable-options','--output-format','terse','--harness-timeout','180','--cbmc-args','--unwinding-assertions']
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
tools=[Path('/home/dombarker/.cargo/bin/cargo-kani'),Path('/home/dombarker/.kani/kani-0.67.0/bin/kani-compiler'),Path('/home/dombarker/.kani/kani-0.67.0/bin/cbmc')]
meta={'schema':'focused-extractor-proof-packet-v1','command':cmd,'cwd':str(W),'files':{str(p.relative_to(W)):sha(p) for p in W.rglob('*') if p.is_file() and 'target' not in p.parts},'tools':{str(p):sha(p) for p in tools if p.is_file()},'runner_sha256':sha(Path(__file__)),'source_binding':json.loads((W/'source-binding.json').read_text()),'expected_time':'Small optimized source-cut compilation, then one named whole-Y1 CBMC gate; no finite-field elimination or whole-stage SDK check.','qualification':'Fixed Y1 native/owned-reference byte equality or bounded fixed-input error frame. Complete carriers; no stubs or universal native/caller/SDK closure.','print_axioms':'N/A: Rust/Kani gate'}
(W/(name+'-input.json')).write_text(json.dumps(meta,indent=2)+'\n')
raise SystemExit(subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(H/'kit/capped.py'),str(receipt),'Optimized compilation and one named unchanged whole-Y1 helper CBMC gate; 180s harness timeout','--','timeout','240',*cmd]))
