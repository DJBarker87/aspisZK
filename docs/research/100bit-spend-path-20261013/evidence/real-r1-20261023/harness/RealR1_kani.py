#!/usr/bin/env python3
"""Focused external harness; never modifies or recompiles a shipped crate."""
import hashlib
import json
import subprocess
import sys
from pathlib import Path

name = sys.argv[1]
assert name in ['faithful-reservation-v1', 'faithful-reservation-v2', 'faithful-reservation-v3', 'faithful-reservation-v4']
root = Path(__file__).resolve().parent.parent
receipt = root / 'native' / name
receipt.mkdir(parents=True, exist_ok=False)
files = ['Cargo.toml', 'RealR1_reservation.rs', 'RealR1_native_reserve.rs', 'RealR1_capped.py']
revision = subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
pins = dict(source_revision=revision, files={n: hashlib.sha256((root/'harness'/n).read_bytes()).hexdigest() for n in files})
(receipt/'inputs.json').write_text(json.dumps(pins, indent=2)+'\n')
host = 'dombarker@100.108.41.90'
workspace = '/home/dombarker/project-offloads/codex-cx-real-r1-20261023'
subprocess.run(['ssh',host,'mkdir -p '+workspace+'/harness'],check=True)
subprocess.run(['scp',*[str(root/'harness'/n) for n in files],host+':'+workspace+'/harness/'],check=True)
remote = r'''
import os,subprocess,time
from pathlib import Path
W=Path(WORKSPACE)
def total():
    caps=[]
    for p in Path('/sys/fs/cgroup').rglob('memory.max'):
        try:
            v=p.read_text().strip()
            if v!='max' and (p.parent/'cgroup.procs').read_text().strip():caps.append(int(v))
        except OSError:pass
    return sum(caps)
start=time.monotonic()
while total()+8*2**30>55*2**30:
    assert time.monotonic()-start<1800
    print('Waiting for capped Kani reservation; no verifier launched.',flush=True)
    time.sleep(30)
os.chdir(W/'harness')
os.environ.update(PATH='/home/dombarker/.cargo/bin:'+os.environ['PATH'],CARGO_TARGET_DIR=str(W/'kani-target'),
                  CARGO_BUILD_JOBS='4',CARGO_PROFILE_DEV_OPT_LEVEL='3',CARGO_NET_OFFLINE='true',RUSTFLAGS='-C opt-level=3 -C link-arg=-Wl,--threads=4')
cmd=['cargo','kani','-j','4','--lib','--exact','--harness','proofs::faithful_reservation',
     '-Z','unstable-options','--output-format','terse','--cbmc-args','--unwinding-assertions','--object-bits','12']
status=subprocess.run(['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G',
                      '-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(W/'harness/RealR1_capped.py'),
                      str(W/'native'/NAME),
                      'Kani MIR compilation then seven-primitive reservation control and payload transport; no finite-field arithmetic',
                      '--','timeout','600',*cmd]).returncode
raise SystemExit(status)
'''.replace('WORKSPACE',repr(workspace)).replace('NAME',repr(name))
result = subprocess.run(['ssh',host,'python3 -'],input=remote,text=True)
for filename in ['receipt.json','time.log','stdout.log','stderr.log']:
    subprocess.run(['scp',host+':'+workspace+'/native/'+name+'/'+filename,str(receipt/filename)],check=True)
sys.exit(result.returncode)
