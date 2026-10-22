"""Review the named tree gate at MemoryHigh; stop CBMC before a cap retry."""
import json, os, signal, time, sys
from pathlib import Path
H=Path('/home/dombarker/project-offloads/codex-cx-prover-commit23-20261021')
name,target=sys.argv[1:3]
while not (H/('receipts/'+name+'/receipt.json')).exists():
 for p in Path('/proc').iterdir():
  if not p.name.isdigit():continue
  try:
   args=(p/'cmdline').read_bytes().replace(b'\0',b' ').decode()
   if not args.startswith('cbmc ') or target not in args:continue
   cg=Path('/sys/fs/cgroup'+(p/'cgroup').read_text().split('0::',1)[1].strip())
   mem=int((cg/'memory.current').read_text())
   print(name+' bytes',mem,flush=True)
   if mem>=6*2**30-64*2**20:
    stop=dict(pid=int(p.name),command=args,memory_current_bytes=mem,cgroup=str(cg),reason='operation-split gate still approaches MemoryHigh; stop for representation/formula review; no unchanged retry')
    (H/(name+'-stop.json')).write_text(json.dumps(stop,indent=2)+'\n')
    os.kill(int(p.name),signal.SIGTERM);print('Stopped only named CBMC process',flush=True);raise SystemExit
  except (OSError,ProcessLookupError):pass
 time.sleep(15)
print('receipt available',flush=True)
