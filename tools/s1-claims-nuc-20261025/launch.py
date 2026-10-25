#!/usr/bin/env python3
"""Launch exactly the prepared ninth source selection in a new owned workspace."""
from pathlib import Path
import subprocess,time,json,shlex
R=Path(__file__).resolve().parents[2];n=9
E=R/f'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021/s1-claims-nuc-extract-run{n}';E.mkdir(exist_ok=False)
H='dombarker@100.108.41.90';W=f'/home/dombarker/project-offloads/s126-real-sdk-20261021/s1-claims-safe-extract-run{n}-20261025';A=f'/private/tmp/s126-claims-safe-host-run{n}-20261025.tar'
steps=[['ssh','-o','BatchMode=yes','-o','ConnectTimeout=8',H,'/usr/bin/mkdir --mode=700 -- '+shlex.quote(W)],['scp','-q','-o','BatchMode=yes',A,H+':'+W+'/input.tar'],['ssh','-o','BatchMode=yes',H,'/usr/bin/tar --no-same-owner -xf '+shlex.quote(W+'/input.tar')+' -C '+shlex.quote(W)]]
for k,cmd in enumerate(steps):
 q=subprocess.run(cmd,capture_output=True,timeout=35);(E/f'stage-{k}-stdout.log').write_bytes(q.stdout);(E/f'stage-{k}-stderr.log').write_bytes(q.stderr);assert q.returncode==0,(k,q.stderr.decode())
code="import os,json\nfrom pathlib import Path\np=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021/s1-claims-safe-extract-run8-20261025/terminal.json')\nassert json.loads(p.read_text())['last_exit_status']==0\nos.utime('/home/dombarker/project-offloads/s126-real-sdk-20261021/s1-claims-safe-extract-run4-20261025/reference/src/lib.rs',None)\nprint('New exact selectors; same source bytes and closed owned warm target')\n"
q=subprocess.run(['ssh','-o','BatchMode=yes',H,'/usr/bin/python3 -I -S -B -'],input=code,text=True,capture_output=True,timeout=15);(E/'cache-invalidation.log').write_text(q.stdout+q.stderr);assert q.returncode==0,q.stderr
cmd=['ssh','-o','BatchMode=yes','-o','ConnectTimeout=8',H,'/usr/bin/python3 -I -S -B '+shlex.quote(W+'/run.py')]
(E/'transport-input.json').write_text(json.dumps(dict(command=cmd,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),host_directory=W,source_archive=A),indent=2)+'\n')
print('Extracting exact wildcard source selectors,6GiB cap',flush=True);start=time.monotonic()
with (E/'transport-stdout.log').open('wb')as out,(E/'transport-stderr.log').open('wb')as err:q=subprocess.run(cmd,stdout=out,stderr=err,timeout=650)
(E/'transport-receipt.json').write_text(json.dumps(dict(exit_status=q.returncode,wall_seconds=time.monotonic()-start,command=cmd),indent=2)+'\n')
print('Remote command terminal, exit',q.returncode,flush=True);print((E/'transport-stderr.log').read_text()[-1300:])
