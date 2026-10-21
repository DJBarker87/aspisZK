#!/usr/bin/env python3
import json,os,subprocess,sys
from pathlib import Path
h=Path(__file__).resolve().parent;os.chdir(h/'generated')
pins=json.loads(Path('source-pins.json').read_text())
base=int(sys.argv[1]) if len(sys.argv)>1 else 140
start=int(sys.argv[2]) if len(sys.argv)>2 else 36
end=int(sys.argv[3]) if len(sys.argv)>3 else len(pins['harnesses'])
for i,target in enumerate(pins['harnesses'][start:end],base):
    name=f'{i:02d}-'+target.split('::')[0]
    cmd=['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','env','PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin','CARGO_BUILD_JOBS=4','python3',str(h/'capped.py'),str(h/'receipts'/name),'--','timeout','--signal=TERM','--kill-after=10s','180s','cargo','kani','--lib','--exact','--harness',target,'--no-assertion-reach-checks','--output-format','old']
    subprocess.run(cmd,check=True)
