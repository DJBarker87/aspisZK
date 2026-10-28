from pathlib import Path
import json,subprocess,os
h=Path('/home/dombarker/project-offloads/codex-cx-lowering2-20261026')
paths=['src','sbf-target-verifier','rustc-diagnostics.py','src/Cargo.lock','build-default-v2/linked.elf']
print(json.dumps({'workspace':str(h),'exists':{n:(h/n).exists() for n in paths},'df':subprocess.check_output(['df','-h',str(h.parent)]).decode()}))
if (h/'sbf-target-verifier').exists():print(subprocess.check_output(['du','-sh',str(h/'sbf-target-verifier')]).decode())
print('cgroup',Path('/proc/self/cgroup').read_text())
cg=Path('/sys/fs/cgroup')/Path('/proc/self/cgroup').read_text().split('0::',1)[1].strip().lstrip('/')
print(json.dumps({'limits':{n:(cg/n).read_text().strip() for n in ['memory.high','memory.max','memory.swap.max','pids.max']}}))
