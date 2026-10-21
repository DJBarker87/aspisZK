#!/usr/bin/env python3
"""Run one read-only analysis in an owned, explicitly capped host scope."""
import hashlib,json,shlex,subprocess,sys
from pathlib import Path
R=Path(__file__).resolve().parents[2];E=R/'docs/research/100bit-spend-path-20261013/evidence/s10-inventory5-20261021'
H='/home/dombarker/project-offloads/codex-cx-s10-inventory5-20261021'
REMOTE='dombarker@100.108.41.90';script=Path(sys.argv[1]);name=script.stem+(('-'+sys.argv[2]) if len(sys.argv)>2 else '')
q=shlex.quote
ssh=['ssh','-o','BatchMode=yes','-o','ConnectTimeout=15',REMOTE]
subprocess.run([*ssh,'mkdir -p '+q(H)],check=True,timeout=30)
subprocess.run(['scp','-q',str(script),REMOTE+':'+H+'/'+script.name],check=True,timeout=60)
revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip()
reservation='/home/dombarker/project-offloads/codex-cx-asq8-kani-20261021/harness/reservation.py'
capped='/home/dombarker/project-offloads/codex-cx-pin-20261020/harness/capped.py'
subprocess.run([*ssh,shlex.join(['python3',reservation,H+'/'+name+'-reservation.json'])],check=True,timeout=60)
argv=['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',capped,H+'/'+name+'-receipt','read-only frozen compiler evidence analysis; no compilation or arithmetic release gate','--','timeout','1150','python3',H+'/'+script.name]
# Timeout bounds an otherwise silent SSH to below the user's 20-minute limit.
p=subprocess.run([*ssh,'cd '+q(H)+' && '+shlex.join(argv)],text=True,capture_output=True,timeout=1190)
(E/(name+'-host.log')).write_text(p.stdout+p.stderr)
for filename in ['receipt.json','time.log','stdout.log','stderr.log']:
    subprocess.run(['scp','-q',REMOTE+':'+H+'/'+name+'-receipt/'+filename,str(E/(name+'-'+filename))],check=True,timeout=60)
subprocess.run(['scp','-q',REMOTE+':'+H+'/'+name+'-reservation.json',str(E/(name+'-reservation.json'))],check=True,timeout=60)
r=dict(target=str(script),source_revision=revision,script_sha256=hashlib.sha256(script.read_bytes()).hexdigest(),command=argv,exit_status=p.returncode,stdout=p.stdout,stderr=p.stderr,print_axioms='N/A: compiler analysis; no Lean theorem')
(E/(name+'-invocation.json')).write_text(json.dumps(r,indent=2)+'\n');print(p.stdout+p.stderr);raise SystemExit(p.returncode)
