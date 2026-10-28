from pathlib import Path
import subprocess,json,time,sys,shutil
D=Path(__file__).resolve().parent

def run(root,label,make):
 for i in range(11):
  name=label if i==0 else label+'-retry-%02d'%i
  out=root/name
  with (root/(name+'-driver.log')).open('w') as f:r=subprocess.run(make(name),stdout=f,stderr=subprocess.STDOUT)
  print(name,r.returncode,flush=True)
  if r.returncode==0:return out
  refused=any(p.exists() and not json.loads(p.read_text()).get('allowed',False) for p in [out/'reservation.json',out/'admission-before.json',out/'admission-barrier.json'])
  if not refused:raise SystemExit(r.returncode)
  if i==10:raise SystemExit('Ten refusal retries exhausted')
  time.sleep(180)
for who in ['baseline','candidate']:
 root=D/'combined'/who
 out=run(root,'build-differential',lambda n:['python3',str(root/'native.py'),n,'cargo','build','--release','--offline','--locked','-j','4','-p','aspis-r1-cost-probe','--example','prover_rw_differential','--features','optimized-terminal,r1p-check,ct-host-prover'])
 if out.name!='build-differential':
  canonical=root/'build-differential';canonical.mkdir(exist_ok=True)
  shutil.copy2(out/'binary-pins.json',canonical/'binary-pins.json')
  (canonical/'accepted-build.json').write_text(json.dumps(dict(accepted_build=str(out),note='Original attempt was refused before compilation; canonical pins refer only to accepted build'),indent=2))
root=D/'combined'
out=run(root,'combined-differential-001',lambda n:['python3',str(root/'run_host.py'),n,json.dumps(['python3',str(root/'corpus.py')])])
audit=run(root,'record-ledger-audit',lambda n:['python3',str(root/'run_host.py'),n,json.dumps(['python3',str(root/'audit-corpus.py')])])
(D/'stage-a-complete.json').write_text(json.dumps(dict(utc=time.time(),differential_receipt=str(out/'receipt/receipt.json')),indent=2)+'\n')
