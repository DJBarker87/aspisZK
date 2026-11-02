"""Read-only reconciliation of stalled-session evidence with the build host."""
from pathlib import Path
import subprocess, json, hashlib, shlex, datetime
R=Path(__file__).resolve().parents[2]
E=R/'evidence/pv-runjoin73-20261102'
P='/home/dombarker/project-offloads/codex-pv-runjoin-20261026/runjoin32-lean'
code=r'''
import pathlib,json,hashlib,subprocess,time,re
p=pathlib.Path(WORKSPACE); e=p/'evidence'
files={q.name:hashlib.sha256(q.read_bytes()).hexdigest() for q in e.iterdir() if q.is_file() and re.search(r'798[0-9][0-9]',q.name)}
results={q.name:json.loads(q.read_text()) for q in e.glob('results-*.json') if re.search(r'798[0-9][0-9]',q.name)}
scopes=subprocess.run(['systemctl','--user','list-units','--all','--plain','--no-legend','pv66-lean-*'],text=True,capture_output=True)
cgroups=[]
for q in pathlib.Path('/sys/fs/cgroup').rglob('*pv66*'):
 if q.is_dir():
  cgroups.append(dict(path=str(q),values={n:(q/n).read_text() for n in ['cgroup.events','memory.current','memory.max','memory.swap.max'] if (q/n).exists()}))
sent=pathlib.Path('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/evidence/sent.txt')
sent_hits=[l for l in sent.read_text().splitlines() if re.search(r'\b798[0-9][0-9]\b',l)]
other=[]
for job in pathlib.Path('/home/dombarker/project-offloads').glob('codex-pv-*'):
 if job.name=='codex-pv-runjoin-20261026':continue
 for q in job.glob('evidence/**/*'):
  if q.is_file() and re.search(r'(^|[-_])798[0-9][0-9]([-_.]|$)',q.name):other.append(str(q))
quiet=pathlib.Path('/home/dombarker/project-offloads/QUIET_WINDOW.json')
print(json.dumps(dict(epoch=time.time(),files=files,results=results,scopes=dict(exit=scopes.returncode,stdout=scopes.stdout,stderr=scopes.stderr),cgroups=cgroups,sent_hits=sent_hits,other_job_hits=other,quiet=json.loads(quiet.read_text()) if quiet.exists() else None)))
'''.replace('WORKSPACE',repr(P))
q=subprocess.run(['ssh','-o','BatchMode=yes','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],text=True,capture_output=True,check=True)
host=json.loads(q.stdout)
checks=[]
for f in E.iterdir():
 if f.name in host['files']:
  checks.append(dict(file=f.name,local_sha256=hashlib.sha256(f.read_bytes()).hexdigest(),host_sha256=host['files'][f.name]))
for name, records in host['results'].items():
 a=int(name[8:13]); local=json.loads((E/f'modules-{a}.json').read_text())
 assert local==records,(a,'module receipt mismatch')
assert all(v['local_sha256']==v['host_sha256'] for v in checks),'host evidence mismatch'
assert host['scopes']['exit']==0
receipts=[json.loads(p.read_text()) for p in sorted(E.glob('receipt-*.json'))]
ids=[r['attempt'] for r in receipts]
assert ids==list(range(79800,79858)),ids
assert len(host['results'])==len(receipts)
assert not host['scopes']['stdout'].strip() and not host['cgroups'],'wait for existing scope'
out=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),host=host,matching_files=checks,charged_attempts=len(receipts),accepted=sum(r['accepted'] for r in receipts),rejected=sum(not r['accepted'] for r in receipts),spent_ids=ids,remaining_budget=97-len(receipts),next_unused_id=79858,spent_audit_ids=[],refusals_uncharged=len(list(E.glob('refusal-*.json'))),existing_scope_or_reservation=False)
(E/'reconciliation-D558.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:out[k] for k in ['charged_attempts','accepted','rejected','remaining_budget','next_unused_id','existing_scope_or_reservation']}))
print('Matched host files:',len(checks),'other job hits:',len(host['other_job_hits']))
