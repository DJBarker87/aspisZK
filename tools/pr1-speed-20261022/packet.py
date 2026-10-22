#!/usr/bin/env python3
from pathlib import Path
import sys,shutil,json,hashlib
h=Path(sys.argv[1]);out=Path(sys.argv[2]);out.mkdir(parents=True,exist_ok=True)
meta={}
for stage in ['baseline','step1']:
 r=h/('pr1-'+stage)
 for receipt in (r/'receipts').glob('*/receipt.json'):
  shutil.copytree(receipt.parent,out/'receipts'/stage/receipt.parent.name,dirs_exist_ok=True)
 for p in r.glob('reservation-*.json'):
  shutil.copyfile(p,out/(stage+'-'+p.name))
 for p in ['docs/research/v8-r0-zk-20261009/z4/z9e.rs','crates/aspis-r1-cost-probe/examples/ct_fixture_gate.rs','crates/aspis-r1-cost-probe/examples/pr1_challenges.rs']:
  shutil.copyfile(r/p,out/(stage+'-'+Path(p).name+'.txt'))
 for p in ['fixture-bin','challenge-bin','complete-bin']:
  b=r/p
  if b.exists():meta[stage+'/'+p]={'sha256':hashlib.sha256(b.read_bytes()).hexdigest(),'bytes':b.stat().st_size}
(out/'host-binaries.json').write_text(json.dumps(meta,indent=2)+'\n')
shutil.copyfile(h/'pr1-step1/elf-identities.json',out/'elf-identities.json')
