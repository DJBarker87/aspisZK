from pathlib import Path
import json,subprocess,sys,time,hashlib,runpy
D=Path('/home/dombarker/project-offloads/codex-pv-extract-20261027');name=sys.argv[1]; cmd=json.loads(sys.argv[2]);O=D/name;O.mkdir()
G=Path('/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy')
a=subprocess.run(['python3',str(G/'reservation.py'),str(O/'admission-before.json')],stdout=open(O/'reservation.log','w'),stderr=subprocess.STDOUT)
if a.returncode:sys.exit(a.returncode)
(O/'target.json').write_text(json.dumps(dict(target=cmd,revision='7599dff5b274d52324ae8681664f6b343f9a81ac',phase='optimized source MIR extraction' if 'charon' in name else 'symbolic Aeneas extraction; preflight removed in private copy',print_axioms='N/A extraction'),indent=2))
start=time.monotonic(); c=['systemd-run','--user','--scope','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(G/'barrier.py'),str(O/'admission-barrier.json'),'/usr/bin/time','-v','-o',str(O/'time.log'),*cmd]
r=subprocess.run(c,stdout=open(O/'output.log','w'),stderr=subprocess.STDOUT)
(O/'receipt.json').write_text(json.dumps(dict(exit=r.returncode,wall_seconds=time.monotonic()-start,revision='7599dff5b274d52324ae8681664f6b343f9a81ac',print_axioms='N/A extraction',time_log=(O/'time.log').read_text() if (O/'time.log').exists() else None),indent=2));print(name,r.returncode)
