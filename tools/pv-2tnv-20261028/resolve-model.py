from pathlib import Path
import json,subprocess,hashlib,re
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-2tnv-20261028/resume'
def read(rev,p):return subprocess.check_output(['git','show',rev+':'+p])
rev='codex/pv-runjoin-20261026'
x=json.loads(read(rev,'evidence/pv-runjoin24-20261027/focused-resolution.json'))['resolved']
cache=json.loads(read(rev,'evidence/pv-runjoin24-20261027/focused-project-cache-check.json'))
cache={r['module'].replace('/','.'):r for r in cache}
epj=json.loads(read(rev,'evidence/pv-runjoin20-20261027/project-hash-check.json'))
for r in epj:cache.setdefault(r['module'].replace('/','.'),r)
external={r['module'].replace('/','.') for r in json.load(open(E/'external-authority.json'))}
ejr=json.loads(read('HEAD','evidence/envj-rebuild-20261026/EJR_final-inventory.json'))
auth={}
for r in ejr['selected']:
 if r.get('resolution'):auth.setdefault(r['module'].replace('/','.'),r)
roots=['R1Z.PV_RunJoin_CanonicalFixtures','R1Z.PV_RunJoin_RootModelTable','R1Z.PV_RunJoin_PathValues16','R1Z.PV_RunJoin_OutputValues16','R1Z.PV_RunJoin_FixtureNullifier','R1Z.PV_RunJoin_OutputCell3917','R1Z.PrivacyR1HeadlineDeployedReal']
seen={};gaps=[]
def visit(m):
 if m in seen or m in external:return
 v=x.get(m)
 if v is None:
  gaps.append((m,'not in pinned runjoin24 resolution'));return
 seen[m]=v.copy();sha=v['sha256']
 if m in auth:
  if not any(r.get('resolution') and r['module'].replace('/','.')==m and r['sha256']==sha for r in ejr['selected']):gaps.append((m,'EJR mismatch'))
 else:
  p=v.get('path');b=read('HEAD',p)
  if hashlib.sha256(b).hexdigest()!=sha:gaps.append((m,'HEAD mismatch'))
 c=cache.get(m)
 if not c:gaps.append((m,'missing object provenance'))
 else:
  seen[m]['cache']=c
  if c.get('prior_own_source_receipts'):
   verified=[]
   for rp in c['prior_own_source_receipts']:
    receipt=json.loads(read(rev,rp));snap=str(Path(rp).parent/receipt['source_snapshot'])
    if receipt['source_sha256']==sha and hashlib.sha256(read(rev,snap)).hexdigest()==sha:verified.append(rp)
   seen[m]['recorded_source_receipts']=verified
   if not verified:gaps.append((m,'unverified historical source'))
 for i in v.get('imports',[]):visit(i)
for m in roots:visit(m)
(E/'model-resolution.json').write_text(json.dumps(dict(roots=roots,resolved=seen,gaps=gaps),indent=2)+'\n')
print('model project closure',len(seen),'gaps',gaps[:30])
