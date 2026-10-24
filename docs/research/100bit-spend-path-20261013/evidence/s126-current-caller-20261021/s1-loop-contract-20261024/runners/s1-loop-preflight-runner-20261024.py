#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,os,subprocess
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');W=H/'s1-loop-contract-preflight-20261024';W.mkdir(exist_ok=False);(W/'src').mkdir()
(W/'Cargo.toml').write_text('[package]\nname="s1-loop-contract-preflight"\nversion="0.0.0"\nedition="2021"\n[workspace]\n')
(W/'src/lib.rs').write_text('''#[cfg(kani)]
#[kani::proof]
fn range_loop_contract() {
 let mut count=0usize;
 #[kani::loop_invariant(count==kani::index())]
 for _i in 0usize..6usize {count+=1;}
 assert_eq!(count,6);
}
''')
subprocess.run(['python3',str(H/'kit/reservation.py'),str(W/'admission-app-scopes.json')],check=True,stdout=subprocess.DEVNULL)
collector='/home/dombarker/project-offloads/r1-circle-sample-wrapper-extraction-v2/collect-cgroups.py';snap=subprocess.check_output(['python3',collector],text=True);(W/'admission-global.json').write_text(snap);inv=json.loads(snap);G=2**30;assert inv['effective_sum_bytes']+2*G<=48*G and inv['MemAvailable_kB']*1024>=4*G
os.environ.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_BUILD_JOBS='1',CARGO_NET_OFFLINE='true',CARGO_TARGET_DIR=str(W/'target'),RUSTFLAGS='-C opt-level=3 -Z mir-opt-level=0 -C overflow-checks=yes')
cmd=['cargo','kani','--manifest-path',str(W/'Cargo.toml'),'--lib','--exact','--harness','range_loop_contract','-j','1','-Z','loop-contracts','-Z','unstable-options','--harness-timeout','45','--no-assertion-reach-checks','--output-format','terse']
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();(W/'input.json').write_text(json.dumps(dict(command=cmd,source_sha256=sha(W/'src/lib.rs'),runner_sha256=sha(Path(__file__)),expected_time='Tiny six-iteration Range loop-contract capability preflight, no project arithmetic or verifier proof.'),indent=2)+'\n')
raise SystemExit(subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=1G','-p','MemoryMax=2G','-p','MemorySwapMax=0','-p','TasksMax=32','python3',str(H/'kit/capped.py'),str(W/'attempt'),'Pinned Kani Range loop-contract capability preflight','--',*cmd]))
