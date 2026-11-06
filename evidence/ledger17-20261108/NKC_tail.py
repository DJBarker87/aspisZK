"""Own serial continuation after all thirty raw groups; never overlaps a scope."""
from pathlib import Path
import json,subprocess,time,sys
E=Path(__file__).resolve().parent
until=time.monotonic()+1800
while True:
 rows=[json.loads(l)for l in(E/'NKC_ATTEMPTS.jsonl').read_text().splitlines()]
 if len(rows)==38 and not(E/'NKC_CLIENT_ACTIVE').exists():break
 if len(rows)>38 or time.monotonic()>until:raise RuntimeError('Unexpected completed count or pending raw queue; no launch')
 time.sleep(1)
assert len({r['attempt']for r in rows})==38
for i in range(30):
 x=json.loads((E/f'NKC_audit/batch{i}/proof{i}.json').read_text())
 assert all(set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}for r in x['results'])
 if x['exit_status']:assert [r['root']for r in x['results']if not r['equal']]==['NHC_DecodeModel.decoder_error']
for i,k,t in [(39,'lean','NKC_HypothesisReview'),(40,'audit','close')]:
 r=subprocess.run([sys.executable,str(E/'NKC_run.py'),f'NKC_L{i:03}',k,t],capture_output=True,text=True)
 print(json.dumps(dict(attempt=i,exit=r.returncode,summary=r.stdout[-350:],error=r.stderr[-500:])),flush=True)
 if r.returncode:sys.exit(r.returncode)
