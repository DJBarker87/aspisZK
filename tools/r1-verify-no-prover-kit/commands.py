#!/usr/bin/env python3
"""Print exact capped B gate commands; never executes them."""
import argparse,json
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);a=p.parse_args();root=a.root.resolve();pins=json.loads(Path(__file__).with_name('source-pins.json').read_text());print(json.dumps([{'label':g['label'],'command':['systemd-run','--user','--scope','--unit','r1-b-no-prover-'+g['label']+'-20261018','--property=MemoryHigh=6G','--property=MemoryMax=8G','--property=MemorySwapMax=0','python3',str(root/'tools/r1-verify-no-prover-kit/governor.py'),'--root',str(root),'--label',g['label'],'--execute-granted'],'native_command':[v.replace('{root}',str(root)) for v in g['command']]} for g in pins['gates']],indent=2))
