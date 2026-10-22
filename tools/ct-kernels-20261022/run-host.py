#!/usr/bin/env python3
from pathlib import Path
import os, subprocess, sys
R=Path(__file__).resolve().parents[2]
name=sys.argv[1];cmd=sys.argv[2:]
subprocess.run(['python3',str(R/'tools/ct-kernels-20261022/reservation.py'),str(R/('reservation-'+name+'.json'))],check=True,stdout=subprocess.DEVNULL)
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_BUILD_JOBS='4',CARGO_NET_OFFLINE='true',CARGO_PROFILE_DEV_OPT_LEVEL='3',RUSTFLAGS='-C link-arg=-Wl,--threads=4',CT_EXPECTED=os.getenv('CT_EXPECTED','Optimized compilation followed by named symbolic kernel gate; no elimination'),CARGO_TARGET_DIR=str(R.parent/'target'))
sys.exit(subprocess.run(['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(R/'tools/ct-kernels-20261022/host-run.py'),name,*cmd],cwd=R,env=env).returncode)
