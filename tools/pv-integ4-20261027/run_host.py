from pathlib import Path
import json,subprocess,sys,time,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-integ4-20261027');name=sys.argv[1];cmd=json.loads(sys.argv[2]);O=D/name;O.mkdir()
G=Path('/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy')
r=subprocess.run(['python3',str(G/'reservation.py'),str(O/'admission-before.json')],stdout=open(O/'reservation.log','w'),stderr=subprocess.STDOUT)
if r.returncode or not json.loads((O/'admission-before.json').read_text()).get('allowed',False):sys.exit(r.returncode or 78)
rev=(D/'source-revision.txt').read_text().strip()
(O/'target.json').write_text(json.dumps(dict(target=cmd,revision=rev,print_axioms='N/A extraction/native run'),indent=2))
r=subprocess.run(['systemd-run','--user','--scope','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(G/'barrier.py'),str(O/'admission-barrier.json'),'python3',str(D/'capped.py'),str(O/'receipt'),name,'--',*cmd],stdout=open(O/'output.log','w'),stderr=subprocess.STDOUT)
status=r.returncode
if status and (O/'admission-barrier.json').exists() and not (O/'receipt/receipt.json').exists():
 admission=json.loads((O/'admission-barrier.json').read_text())
 if not admission['allowed']:
  (O/'refusal-classification.json').write_text(json.dumps(dict(raw_exit=status,classified_exit=78,reason='reservation barrier refused before command execution'),indent=2))
  status=78
print(name,status);sys.exit(status)
