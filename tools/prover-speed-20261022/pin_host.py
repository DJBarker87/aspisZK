#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,subprocess,sys
suffix=sys.argv[1] if len(sys.argv)>1 else ""
H=Path('/home/dombarker/project-offloads/codex-cx-prover-speed-20261022')
for mode in ['research','v2']:
 R=H/mode
 pins={str(p.relative_to(R)):hashlib.sha256(p.read_bytes()).hexdigest() for p in R.rglob('*') if p.is_file()}
 (H/(mode+suffix+'-source-pins.json')).write_text(json.dumps(pins,sort_keys=True,indent=2)+'\n')
 if (H/'bin'/(mode+suffix)).exists():
  b=H/'bin'/(mode+suffix)
  d=subprocess.run(['objdump','-d',str(b)],text=True,capture_output=True,check=True).stdout
  (H/(mode+suffix+'-sha-disassembly.txt')).write_text('\n'.join(x for x in d.splitlines() if any(k in x for k in ['sha256rnds2','sha256msg1','sha256msg2']))+'\n')
(H/'tools-pins.json').write_text(json.dumps({p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in (H/'tools').iterdir() if p.is_file()},indent=2)+'\n')
