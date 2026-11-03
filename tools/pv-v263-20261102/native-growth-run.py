"""N90125: new MIR type-inference gate, one optimized no-swap scope."""
from pathlib import Path
import subprocess,json,shlex,time,hashlib,re,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-v263-20261102';P='/home/dombarker/project-offloads/codex-pv-runjoin-20261026/v263-native';H='dombarker@100.108.41.90';a='N90125'
assert not (E/(a+'-transport.json')).exists(),'submitted ID: recover original logs'
for f in E.glob(a+'-refusal-*.json'):
 assert time.time()>=json.loads(f.read_text())['epoch']+180,'mandatory refusal cooldown'
def ssh(cmd):
 q=subprocess.run(['ssh',H,cmd],capture_output=True,text=True)
 assert q.returncode!=255,'transport failed before submission: cooldown/recovery rules apply'
 return q
code='''import pathlib,re,json
root=pathlib.Path('/home/dombarker/project-offloads');hits=[]
for job in root.glob('codex-pv-*'):
 if job.name=='codex-pv-runjoin-20261026':continue
 for q in job.glob('evidence/**/*'):
  if q.is_file() and re.search(r'(^|[-_])N?90124([-_.]|$)',q.name):hits.append(str(q))
sent=root/'r1-privacy-build-integration-20261019/evidence/sent.txt'
lines=[l for l in sent.read_text().splitlines() if len(l.split())>2 and l.split()[2] in ['90124','N90125']]
print(json.dumps(dict(attempt='N90125',other_receipt_hits=hits,sent_hits=lines,check_timing='before staging and launch')))
'''
q=ssh('python3 -c '+shlex.quote(code));assert q.returncode==0,q.stderr
idcheck=json.loads(q.stdout);(E/(a+'-id-audit.json')).write_text(json.dumps(idcheck,indent=2)+'\n')
assert not idcheck['other_receipt_hits'] and not idcheck['sent_hits'],idcheck
admit='python3 /home/dombarker/project-offloads/codex-pv-runjoin-20261026/reservation-existing.py '+P+'/'+a+'-reservation.json > '+P+'/'+a+'-reservation.log 2>&1'
def admission():
 q=ssh(admit)
 for suffix in ['reservation.json','reservation.log']:
  r=ssh('cat '+shlex.quote(P+'/'+a+'-'+suffix));assert r.returncode==0
  (E/(a+'-'+suffix)).write_text(r.stdout)
 x=json.loads((E/(a+'-reservation.json')).read_text())
 if q.returncode or x.get('allowed') is not True:
  x.update(epoch=time.time(),exit=q.returncode,compiler_started=False)
  (E/(a+'-refusal-'+str(time.time_ns())+'.json')).write_text(json.dumps(x,indent=2)+'\n')
  print('REFUSED uncharged; full 180s cooldown; same ID',x.get('reason'));sys.exit(78)
 return x
admission() # Required receipt before staging.
files=list((E/'inputs').rglob('*'))+[E/'frozen-source.json',R/'tools/pv-v263-20261102/native-growth.rs',R/'tools/pv-v263-20261102/native-growth-host.py']
payload={str(p.relative_to(R)):p.read_text() for p in files if p.is_file()}
rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
for f,s in payload.items():assert subprocess.check_output(['git','show',rev+':'+f])==s.encode(),('commit input',f)
code="import pathlib,json,sys;p=pathlib.Path("+repr(P)+");x=json.load(sys.stdin)\nfor f,s in x.items():\n q=p/f;q.parent.mkdir(parents=True,exist_ok=True);q.write_text(s)"
q=subprocess.run(['ssh',H,'python3 -c '+shlex.quote(code)],input=json.dumps(payload),text=True,capture_output=True);assert q.returncode==0,q.stderr
cmd=['systemd-run','--user','--scope','--quiet','--unit=pv-v263-native-'+a,'-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','/usr/bin/time','-v','-o',P+'/'+a+'-time.log','python3',P+'/tools/pv-v263-20261102/native-growth-host.py',P]
check='python3 -c '+shlex.quote('import json;assert json.load(open('+repr(P+'/'+a+'-reservation.json')+'))["allowed"] is True')
print('Expected time: compilation and fifteen scoped thread pushes per representative payload; no arithmetic gate',flush=True)
q=subprocess.run(['ssh',H,'bash -o pipefail -c '+shlex.quote(admit+' && '+check+' && '+shlex.join(cmd)+' > '+P+'/'+a+'-stdout.log 2>&1')],capture_output=True,text=True)
for f in ['reservation.json','reservation.log']:
 r=ssh('cat '+shlex.quote(P+'/'+a+'-'+f));assert r.returncode==0;(E/(a+'-'+f)).write_text(r.stdout)
x=json.loads((E/(a+'-reservation.json')).read_text())
if x.get('allowed') is not True:
 x.update(epoch=time.time(),exit=q.returncode,compiler_started=False)
 (E/(a+'-refusal-'+str(time.time_ns())+'.json')).write_text(json.dumps(x,indent=2)+'\n')
 print('REFUSED uncharged after staging; full 180s cooldown; same ID');sys.exit(78)
(E/(a+'-transport.json')).write_text(json.dumps(dict(exit=q.returncode,stdout=q.stdout,stderr=q.stderr,command=cmd,source_revision=rev,input_hashes={p:hashlib.sha256(s.encode()).hexdigest() for p,s in payload.items()}),indent=2)+'\n')
for f in ['time.log','stdout.log','native-results.json','growth-observations.json']:
 r=ssh('cat '+shlex.quote(P+'/'+a+'-'+f));assert r.returncode==0,r.stderr;(E/(a+'-'+f)).write_text(r.stdout)
tim=(E/(a+'-time.log')).read_text()
def match(p):
 m=re.search(p,tim);return m[1] if m else None
wall=0
for part in match(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([0-9:.]+)').split(':'):wall=wall*60+float(part)
results=json.loads((E/(a+'-native-results.json')).read_text())
receipt=dict(attempt=a,exit=q.returncode,admission_allowed=True,admission_exit=0,admission_and_launch_same_shell=True,
 source_revision=rev,targets=[r['target'] for r in results],wall_seconds=wall,
 peak_rss_bytes=int(match(r'Maximum resident set size \(kbytes\): (\d+)'))*1024,
 swaps=int(match(r'Swaps: (\d+)')),axioms='not applicable: native finite growth validation',
 rustc='1.94.1',features=['r1p-check','ct-host-prover'],trace_counterpart='not used',
 profile=dict(opt_level=3,panic='abort',overflow_checks=False,debug_assertions=False),
 coverage='isolated std handle-vector gate, representative payloads; not actual callback execution or full-crate feature build',
 accepted=q.returncode==0 and all(r.get('expected') for r in results))
(E/(a+'-receipt.json')).write_text(json.dumps(receipt,indent=2)+'\n')
print('RECEIPT',a,'accepted',receipt['accepted'],'wall',wall,'RSS',receipt['peak_rss_bytes'],'swap',receipt['swaps'])
sys.exit(0 if receipt['accepted'] else 1)
