"""One N90122 scope: changed profile/nested TLS/abort checks, not an unchanged rerun."""
from pathlib import Path
import subprocess,json,shlex,time,hashlib,re,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-v263-20261102';P='/home/dombarker/project-offloads/codex-pv-runjoin-20261026/v263-native';H='dombarker@100.108.41.90';a='N90122'
assert not (E/(a+'-transport.json')).exists(),'submitted ID: recover original logs'
files=list((E/'inputs').rglob('*'))+[R/'tools/pv-v263-20261102/native-abort.rs',R/'tools/pv-v263-20261102/native-abort-host.py']
payload={str(p.relative_to(R)):p.read_text() for p in files if p.is_file()}
code="import pathlib,json,sys;p=pathlib.Path("+repr(P)+");x=json.load(sys.stdin)\nfor f,s in x.items():\n q=p/f;q.parent.mkdir(parents=True,exist_ok=True);q.write_text(s)"
subprocess.run(['ssh',H,'python3 -c '+shlex.quote(code)],input=json.dumps(payload),text=True,check=True)
cmd=['systemd-run','--user','--scope','--quiet','--unit=pv-v263-native-'+a,'-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','/usr/bin/time','-v','-o',P+'/'+a+'-time.log','python3',P+'/tools/pv-v263-20261102/native-abort-host.py',P]
admit='python3 /home/dombarker/project-offloads/codex-pv-runjoin-20261026/reservation-existing.py '+P+'/'+a+'-reservation.json > '+P+'/'+a+'-reservation.log 2>&1'
check='python3 -c '+shlex.quote('import json;assert json.load(open('+repr(P+'/'+a+'-reservation.json')+'))["allowed"] is True')
print('Expected time: compilation; finite nested TLS/abort checks only',flush=True)
q=subprocess.run(['ssh',H,'bash -o pipefail -c '+shlex.quote(admit+' && '+check+' && '+shlex.join(cmd)+' > '+P+'/'+a+'-stdout.log 2>&1')],capture_output=True,text=True)
(E/(a+'-transport.json')).write_text(json.dumps(dict(exit=q.returncode,stdout=q.stdout,stderr=q.stderr,command=cmd,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),input_hashes={p:hashlib.sha256(s.encode()).hexdigest() for p,s in payload.items()}),indent=2)+'\n')
for f in ['reservation.json','reservation.log','time.log','stdout.log','native-results.json']:
 r=subprocess.run(['ssh',H,'cat '+shlex.quote(P+'/'+a+'-'+f)],capture_output=True,text=True);(E/(a+'-'+f)).write_text(r.stdout+r.stderr)
x=json.loads((E/(a+'-reservation.json')).read_text())
if not x.get('allowed'):
 print('REFUSED: no native process admitted; retain ID and wait 180 seconds',flush=True);sys.exit(78)
assert q.returncode==0,(q.returncode,q.stderr)
print((E/(a+'-stdout.log')).read_text(),end='')
