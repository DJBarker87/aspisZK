"""Execute the canonical recovery builder with explicit continuation scheduling.
Only EJS files are created by this adapter; canonical builder remains unchanged.
"""
from pathlib import Path
import hashlib, os
T=Path('/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence')
p=T/'EJR_build_host.py'
s=p.read_text()
assert hashlib.sha256(p.read_bytes()).hexdigest()=='57f8ce56a0415520e457df78776d473170473aa8c78c910c749dd890be168802'
assert os.environ.get('EJR_CUMULATIVE_BUILD_LIMIT')=='1600'
def replace(old,new):
 global s
 assert s.count(old)==1, old
 s=s.replace(old,new)
replace("pending=[r for r in rows if r['key'] not in attempted or r['key'] in repair_keys]", """assert 30800 <= attempt <= 31600, attempt
assert len(past) >= 800
excluded={'R1Z/EventsR1P2','R1Z/SimCostOuterRetry6'}
pending=[r for r in rows if (r['key'] not in attempted or r['key'] in repair_keys) and r['module'] not in excluded]
bykey={r['key']:r for r in rows}
priority=set()
def mark(k):
 if k in priority or k not in bykey:return
 priority.add(k)
 r=bykey[k]
 for m in r['imports']:
  own=r['workspace']+':'+m
  if own in bykey:mark(own)
  else:
   for ws in roots:mark(ws+':'+m)
for r in rows:
 if r['module'].startswith('R1Z/') or 'ProverCommit' in r['module'] or 'PrivacyR1HeadlineDeployedReal' in r['module']:mark(r['key'])
""")
replace("ready.sort(key=lambda rd:(not rd[0]['module'].startswith('R1Z/'),rd[0]['workspace']!='joint',rd[0]['module']))", "ready.sort(key=lambda rd:(rd[0]['key'] not in repair_keys, rd[0]['key'] not in priority, not rd[0]['module'].startswith('R1Z/'),rd[0]['workspace']!='joint',rd[0]['module']))")
replace("label='EJR-'+str(attempt);admission=admit(label)", "assert 30800 <= attempt < 31600 and attempt <= 34999, attempt\n label='EJR-'+str(attempt);admission=admit(label)")
replace("budget=800,next_attempt=attempt", "budget=budget,next_attempt=attempt")
(T/'EJS_executed-builder.py').write_text(s)
exec(compile(s,str(p),'exec'),{'__name__':'__main__','__file__':str(p)})
