#!/usr/bin/env python3
"""Read ONLY owned NUC runtime text; launch snapshot is not a terminal verdict, never target/binary directories."""
from pathlib import Path
import subprocess,json,hashlib,sys,re
label=sys.argv[1];assert re.fullmatch(r's1-native-current-stream-terminal-v[0-9]+',label)
R=Path(__file__).resolve().parents[2];E=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021'/label;E.mkdir(exist_ok=False)
code='''from pathlib import Path
import resource,json,hashlib,signal
resource.setrlimit(resource.RLIMIT_AS,(512*2**20,512*2**20));signal.alarm(30)
base=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');files={};total=0
for n in [1]:
 W=base/f'native-current-stream-20261025-v{n}';assert W.is_dir()and not W.is_symlink()
 selected=[W/'nuc.py',W/'plan.json']
 if (W/'queue.py').exists():selected.append(W/'queue.py')
 for d in W.glob('run-*'):
  if not (d/'outer-terminal.json').exists():continue
  json.loads((d/'outer-terminal.json').read_text())
  assert d.is_dir()and not d.is_symlink()
  selected += [p for p in d.iterdir()if p.is_file()]
 for p in selected:
  assert not p.is_symlink()and p.suffix in ['.py','.json','.log','.txt']
  data=p.read_bytes();assert len(data)<8*2**20;total+=len(data);assert total<24*2**20
  files[f'v{n}/'+str(p.relative_to(W))]=dict(text=data.decode(),sha256=hashlib.sha256(data).hexdigest())
print(json.dumps(dict(source_only=True,files=files)))
'''
cmd=['ssh','-o','BatchMode=yes','-o','ConnectTimeout=8','dombarker@100.108.41.90','/usr/bin/python3 -I -S -B -'];q=subprocess.run(cmd,input=code,capture_output=True,text=True,timeout=40);(E/'transport-stderr.log').write_text(q.stderr);assert q.returncode==0,q.stderr
j=json.loads(q.stdout)
for rel,row in j['files'].items():
 p=E/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(row['text']);assert hashlib.sha256(p.read_bytes()).hexdigest()==row['sha256']
(E/'collection.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',command=cmd,files={rel:r['sha256']for rel,r in j['files'].items()},source_only=True,compiler_or_verifier_launched=False),indent=2)+'\n');print(json.dumps(dict(collected=len(j['files']),source_only=True)))
