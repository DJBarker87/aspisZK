#!/usr/bin/env python3
from pathlib import Path
import json,hashlib,time
H=Path('/home/dombarker/project-offloads/codex-pv-l3-20261026');O=H/'dual-evidence';cg=Path('/sys/fs/cgroup'+Path('/proc/self/cgroup').read_text().split('0::')[1].strip());t=time.monotonic();checks={}
for name in ['A','B']:
 pins=json.loads((H/(name+'-source.json')).read_text());bad=[]
 for p,v in pins['files'].items():
  if hashlib.sha256((H/('dual-'+name)/p).read_bytes()).hexdigest()!=v['sha256']:bad.append(p)
 checks[name]=dict(source_revision=pins['revision'],files=len(pins['files']),mismatches=bad)
 assert not bad,bad
rec=json.loads((O/'A/receipt.json').read_text());assert hashlib.sha256((H/'bin/devnet_spend-A').read_bytes()).hexdigest()==rec['binary_sha256']
ext=json.loads((O/'A/extraction.json').read_text());assert hashlib.sha256((O/'A/full-disassembly.txt').read_bytes()).hexdigest()==ext['full_disassembly_sha256']
assert not (H/'bin/devnet_spend-B').exists()
checks.update(exit_status=0,wall_seconds=time.monotonic()-t,target='validate source archives unchanged after builds; retained A binary/disassembly hashes; B absent',limits={n:(cg/n).read_text().strip() for n in ['memory.high','memory.max','memory.swap.max','pids.max']},cgroup_memory_peak_bytes=int((cg/'memory.peak').read_text()),cgroup_swap_peak_bytes=int((cg/'memory.swap.peak').read_text()),print_axioms='N/A (no Lean)')
(O/'post-build-validation.json').write_text(json.dumps(checks,indent=2)+'\n');print(json.dumps(checks))
