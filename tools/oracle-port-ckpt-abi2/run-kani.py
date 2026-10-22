#!/usr/bin/env python3
"""Host only: one capped Kani target, source and reservation validation first."""
from pathlib import Path
import json,os,subprocess,sys
R=Path(__file__).resolve().parents[2]
name,target=sys.argv[1:]
subprocess.run(['python3',str(R/'tools/oracle-port-ckpt-abi2/reservation.py'),str(R/('reservation-'+name+'.json'))],check=True,stdout=subprocess.DEVNULL)
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_TARGET_DIR=str(R/'kani-target'),CARGO_BUILD_JOBS='4',CARGO_NET_OFFLINE='true',CARGO_PROFILE_DEV_OPT_LEVEL='3',RUSTFLAGS='-C link-arg=-Wl,--threads=4',CKPT_EXPECTED='Kani compilation then '+target+' symbolic byte/codec checking; no field arithmetic or elimination')
cmd=['cargo','kani','--manifest-path','tools/oracle-port-ckpt-abi2/Cargo.toml','--lib','--exact','--harness',(target if '::' in target else 'proofs::'+target),'-Z','function-contracts','-Z','stubbing','--no-assertion-reach-checks','--solver','kissat','--output-format','old','-Z','unstable-options','--cbmc-args','--object-bits',('8' if target=='encode_e_contract' else '12' if target.startswith('reader_proofs::') else '16'),'--unwinding-assertions']
sys.exit(subprocess.run(['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3','tools/oracle-port-ckpt-abi2/host-run.py',name,'timeout','300',*cmd],cwd=R,env=env).returncode)
