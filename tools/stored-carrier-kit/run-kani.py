#!/usr/bin/env python3
"""Single capped optimized symbolic source-cut gate, with reservation receipt."""
from pathlib import Path
import os,subprocess,sys
R=Path(__file__).resolve().parents[2];K=R/'tools/stored-carrier-kit'
name,target=sys.argv[1:]
subprocess.run(['python3',str(K/'reservation.py'),str(R/('reservation-'+name+'.json'))],check=True)
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_TARGET_DIR=str(R/'kani-target'),CARGO_BUILD_JOBS='4',CARGO_NET_OFFLINE='true',CARGO_PROFILE_DEV_OPT_LEVEL='3',RUSTFLAGS='-C link-arg=-Wl,--threads=4',CKPT_EXPECTED='optimized Kani compilation then '+target+' guard and slice-identity checking; no arithmetic elimination')
cmd=['cargo','kani','--manifest-path','tools/stored-carrier-kit/Cargo.toml','--lib','--exact','--harness','proofs::'+target,'--no-assertion-reach-checks','--solver','kissat','--output-format','old','-Z','unstable-options','--cbmc-args','--object-bits','12','--unwinding-assertions']
sys.exit(subprocess.run(['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(K/'host-run.py'),name,'timeout','--signal=TERM','--kill-after=10s','240',*cmd],cwd=R,env=env).returncode)
