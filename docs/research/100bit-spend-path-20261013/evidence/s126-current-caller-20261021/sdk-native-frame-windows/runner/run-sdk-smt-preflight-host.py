#!/usr/bin/env python3
"""Smallest verified-copy bridge with Z3, to localize a caller SMT conversion error."""
from pathlib import Path
import subprocess,hashlib,json,os,sys,signal,re
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');B=Path('/home/dombarker/.kani/kani-0.67.0/bin')
flat='flat-structs' in sys.argv[1:];tag='sdk-std-copy-smt-preflight-'+('v2' if flat else 'v1');O=H/tag;O.mkdir(exist_ok=True)
normal=H/'receipts/sdk-std-copy-bridge-pipeline-v1/stdout.log'
paths=re.findall(r'Running: `goto-cc (\S+\.symtab\.out)',normal.read_text());assert len(paths)==1,paths
program=Path(paths[0].replace('.symtab.out','.out'));assert program.is_file()
z=H/'z3-tool-v1/bin/z3'
os.environ['PATH']=str(z.parent)+':'+os.environ.get('PATH','/usr/bin:/bin')
cmd=[str(B/'cbmc'),'--no-malloc-may-fail','--no-undefined-shift-check','--no-signed-overflow-check','--nan-check','--no-self-loops-to-assumptions','--no-pointer-primitive-check','--object-bits','16','--unwind','8',*(['--bitwuzla','--external-smt2-solver',str(z)] if flat else ['--z3']),'--slice-formula','--unwinding-assertions','--json-ui',str(program)]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
if 'run' not in sys.argv[1:]:
 subprocess.run(['python3',str(H/'kit/reservation.py'),str(H/(tag+'-admission.json'))],check=True,stdout=subprocess.DEVNULL)
 (H/(tag+'-input.json')).write_text(json.dumps(dict(command=cmd,program_sha256=sha(program),normal_pipeline_sha256=sha(normal),source_sha256=sha(H/'sdk-std-copy-frame-v1/src/lib.rs'),sat_proof_receipt_sha256=sha(H/'receipts/sdk-std-copy-bridge-join-v1/receipt.json'),tool_pins={str(p):sha(p) for p in [B/'cbmc',z]},runner_sha256=sha(Path(__file__)),qualification=__doc__),indent=2)+'\n')
 raise SystemExit(subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=1G','-p','MemoryMax=2G','-p','MemorySwapMax=0','-p','TasksMax=32','python3',str(H/'kit/capped.py'),str(H/'receipts'/tag),'Small verified std copy SMT backend preflight; no compilation or full caller replay','--','python3',__file__,'run',*(['flat-structs'] if flat else [])]))
with (O/'cbmc.log').open('w') as f:
 p=subprocess.Popen(cmd,stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
 try:p.wait(timeout=60)
 except subprocess.TimeoutExpired:os.killpg(p.pid,signal.SIGKILL);p.wait();raise
try:
 items=json.loads((O/'cbmc.log').read_text());rows=[{k:v for k,v in r.items() if k!='trace'} for item in items for r in item.get('result',[])]
 (O/'properties-without-traces.json').write_text(json.dumps(rows,indent=2)+'\n')
except ValueError:pass
raise SystemExit(p.returncode)
