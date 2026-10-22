#!/usr/bin/env python3
from pathlib import Path
import subprocess,json,hashlib,difflib
E=Path('docs/research/100bit-spend-path-20261013/evidence/prover-speed-20261022');H='/home/dombarker/project-offloads/codex-cx-prover-speed-20261022';host='dombarker@100.108.41.90'
subprocess.run(['ssh',host,'python3 '+H+'/tools/pin_host.py -fine'],check=True)
summary={}
for mode,rev in [('research','7f13d411b8f6af7dbd17d23e79fd24bf9998e913'),('v2','2b7a80b65a')]:
 for stage in ['build','run']:subprocess.run(['scp','-r',host+':'+H+'/receipts/'+mode+'-fine-'+stage,str(E/'receipts')],check=True)
 for name in [mode+'-fine-source-pins.json',mode+'-fine-sha-disassembly.txt']:
  subprocess.run(['scp',host+':'+H+'/'+name,str(E/name)],check=True)
 pins=json.loads((E/(mode+'-fine-source-pins.json')).read_text());old=json.loads((E/(mode+'-source-pins.json')).read_text());changed=[p for p,h in pins.items() if old.get(p)!=h];assert sorted(changed)==['crates/aspis-r1-cost-probe/src/r1_wire.rs','docs/research/v8-r0-zk-20261009/z4/z9e.rs'],changed
 diff=[]
 for p in changed:
  a=subprocess.check_output(['git','show',rev+':'+p],text=True);b=subprocess.check_output(['ssh',host,'cat '+H+'/'+mode+'/'+p],text=True);assert hashlib.sha256(b.encode()).hexdigest()==pins[p];diff.extend(difflib.unified_diff(a.splitlines(keepends=True),b.splitlines(keepends=True),fromfile='a/'+p,tofile='b/'+p))
 (E/(mode+'-fine-changed-files.patch')).write_text(''.join(diff))
 O=E/'receipts'/(mode+'-fine-run');rows=[json.loads(l.removeprefix('SPEED_ROW ')) for l in (O/'stdout.log').read_text().splitlines() if l.startswith('SPEED_ROW ')];emit=[list(map(float,l.split()[1:])) for l in (O/'stderr.log').read_text().splitlines() if l.startswith('SPEED_EMIT_SPLIT ')];assert len(rows)==len(emit)==2
 for r,e in zip(rows,emit):
  assert r['verified_strict_dense'] and r['attempts']==1 and r['proof_bytes']==57607
  r['emit_lifts_qprime_bcond']=e
 summary[mode]=rows
(E/'fine-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
subprocess.run(['scp',host+':'+H+'/tools-pins.json',str(E/'fine-tools-pins.json')],check=True)
