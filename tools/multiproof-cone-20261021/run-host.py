#!/usr/bin/env python3
from pathlib import Path
import os,subprocess,sys
R=Path(__file__).resolve().parents[2];T=Path(__file__).resolve().parent
os.chdir(R)
name=sys.argv[1];selectors=sys.argv[2:]
env={**os.environ,'PATH':'/home/dombarker/.cargo/bin:'+os.environ['PATH'],'CARGO_BUILD_JOBS':'4','CARGO_NET_OFFLINE':'true','RUSTFLAGS':'-C opt-level=3 -C link-arg=-Wl,--threads=4'}
subprocess.run(['python3',str(T/'reservation.py'),str(R/('reservation-'+name+'.json'))],check=True,stdout=subprocess.DEVNULL)
cmd=['cargo','kani','--manifest-path',str(T/'Cargo.toml'),'--lib','--exact','--solver','cadical','--output-format','old','--no-assertion-reach-checks','-Z','function-contracts','-Z','stubbing','-Z','unstable-options','--harness-timeout','240']
for selector in selectors:cmd+=['--harness','proofs::'+selector]
cmd+=['--cbmc-args','--unwinding-assertions']
raise SystemExit(subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(T/'host-run.py'),name,'timeout','900',*cmd],env=env))
