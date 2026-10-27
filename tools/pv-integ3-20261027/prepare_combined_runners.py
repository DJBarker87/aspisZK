"""NEXT-CYCLE ONLY: install pinned runners, never execute the planned gates."""
from pathlib import Path
import subprocess,json,shlex,sys,hashlib
assert len(sys.argv)==2,'usage: prepare_combined_runners.py FULL_REVIEWED_CANDIDATE_REV'
rev=subprocess.check_output(['git','rev-parse','--verify',sys.argv[1]+'^{commit}'],text=True).strip();assert rev==sys.argv[1], 'Require full reviewed revision'
H='dombarker@100.108.41.90';D='/home/dombarker/project-offloads/codex-pv-integ1-20261027/d298';P=Path(__file__).resolve().parent
payload={}
for side in ['baseline','candidate']:
 root=D+'/combined/'+side
 for name in ['native.py','run_host.py','capped.py','capped-template.py','reservation.py']:
  payload[side+'/'+name]=(P/name).read_text().replace(D,root)
for src,dst in [('combined-corpus.py','corpus.py'),('combined-timing.py','timing.py')]:payload[dst]=(P/src).read_text()
for name in ['run_host.py','capped.py']:payload[name]=(P/name).read_text().replace(D,D+'/combined')
payload['source-revision.txt']=rev+'\n'
code='''from pathlib import Path
import json,hashlib
H=Path(ROOT);payload=PAYLOAD
for side,pin in [('baseline',BASE),('candidate',REV)]:
 assert (H/side/'source-revision.txt').read_text().strip()==pin
 assert (H/side/'source/Cargo.toml').exists()
for rel,source in payload.items():
 p=H/rel;assert not p.exists(),p;p.write_text(source)
(H/'quiet-preflight.py').write_bytes((Path('/home/dombarker/project-offloads/codex-pv-op223-20261027/quiet-preflight.py')).read_bytes())
(H/'runner-pins.json').write_text(json.dumps({rel:hashlib.sha256(source.encode()).hexdigest() for rel,source in payload.items()},indent=2)+'\\n')
print('Prepared only; no build, differential or timing launched')
'''.replace('ROOT',repr(D+'/combined')).replace('PAYLOAD',repr(payload)).replace('BASE',repr(subprocess.check_output(['git','rev-parse','c57a344726'],text=True).strip())).replace('REV',repr(rev))
subprocess.run(['ssh',H,'python3','-'],input=code,text=True,check=True)
