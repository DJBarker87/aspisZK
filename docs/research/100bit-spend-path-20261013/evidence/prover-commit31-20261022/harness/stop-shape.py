from pathlib import Path
import os,signal,json,sys
H=Path('/home/dombarker/project-offloads/codex-cx-prover-commit31-20261022')
rows=[]
for p in Path('/proc').iterdir():
 if not p.name.isdigit():continue
 try:
  args=(p/'cmdline').read_bytes().split(b'\0')
  if args[:3]==[b'timeout',b'600',b'cargo'] and (p/'cwd').resolve()==H/sys.argv[1]:
   rows.append(dict(pid=int(p.name),args=[a.decode() for a in args if a],reason=sys.argv[3]))
   os.kill(int(p.name),signal.SIGTERM)
 except (OSError,ProcessLookupError):pass
(H/(sys.argv[2]+'-stop.json')).write_text(json.dumps(rows,indent=2)+'\n')
assert len(rows)==1,rows
