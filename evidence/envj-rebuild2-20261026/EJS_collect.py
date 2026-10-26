"""Collect text-only EJS receipts; never copy objects or other live workspaces."""
from pathlib import Path
import subprocess, json, shlex, re
O=Path(__file__).parent
remote='''from pathlib import Path
import json
T=Path('/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence')
rs=[json.loads(l) for l in (T/'EJR_attempts.jsonl').read_text().splitlines() if l.strip()]
rs=[r for r in rs if 30800 <= r['attempt'] <= 34999]
files={}
for r in rs:
 for prefix in ['out-','time-','sha-']:
  p=T/(prefix+str(r['attempt'])+('.txt' if prefix=='sha-' else '.log'))
  if p.exists():files['EJS_'+p.name]=p.read_text()
 p=Path(r['admission']['receipt'])
 if p.exists(): files['EJS_'+p.name]=p.read_text()
 for retry in range(r['admission'].get('retries',0)+1):
  for ext in ['json','log']:
   q=T/('EJR-'+str(r['attempt'])+'-reservation-'+str(retry)+'.'+ext)
   if q.exists():files['EJS_'+q.name]=q.read_text()
for p in list(T.glob('EJS_*.json'))+list(T.glob('EJS_*.jsonl'))+list(T.glob('EJS_*.log')):
 if 'payload' not in p.name:files[p.name]=p.read_text()
for name in ['EJS_builder.log','EJS_initial-reservation.json','EJS_initial-reservation.log','EJS_executed-builder.py','EJR_progress.json']:
 p=T/name
 if p.exists():files['EJS_'+name.removeprefix('EJS_')]=p.read_text()
print(json.dumps(dict(records=rs,files=files,reuses=[json.loads(l) for l in (T/'EJR_reuses.jsonl').read_text().splitlines() if l.strip()])))
'''
d=json.loads(subprocess.check_output(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(remote)],text=True))
R=O/'receipts';R.mkdir(exist_ok=True)
for name,s in d['files'].items():(R/name).write_text(s)
for r in d['records']:
 s=d['files']['EJS_out-'+str(r['attempt'])+'.log']
 r['full_axioms_reports']=re.findall(r"'[^\n]*?' (?:depends on axioms:\s*\[[^]]*\]|does not depend on any axioms)",s,re.S)
 r['unsupported_printed_axioms']=sorted({a for b in re.findall(r'depends on axioms:\s*\[([^]]*)\]',s,re.S) for a in b.replace(',',' ').split()}-{'propext','Classical.choice','Quot.sound'})
 r['continuation_revision']='a38d3dc536'
 r['canonical_recovery_revision']=r['source_revision']
 r['source_revision']=r['source_blob_revision'] if re.fullmatch('[0-9a-f]{40}',r['source_blob_revision']) else 'fbda5d86aa33abba917a064a44f89b9ed806d625'
 if not re.fullmatch('[0-9a-f]{40}',r['source_blob_revision']):r['source_revision_qualification']='Committed EJS diagnostic source or exact archive member pinned by formatter profile manifest; historical origin qualifier retained in source_blob_revision.'
 if not r['errors'] and r['lean_exit']!=0:r['errors']=[l for l in s.splitlines() if 'error' in l.lower() or 'must be contained' in l]
 if r['unsupported_printed_axioms']:r['validation_exit']=90
(O/'EJS_reuses.json').write_text(json.dumps(d['reuses'],indent=2)+'\n')
rs=d['records'];(O/'EJS_attempts.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in rs))
s=dict(attempts=len(rs),compiler_passes=sum(r['lean_exit']==0 for r in rs),validation_passes=sum(r['validation_exit']==0 for r in rs),next_attempt=30800+len(rs),peak_rss_kib=max((r['peak_rss_kib'] or 0 for r in rs),default=0),swaps=sum(r['swaps'] or 0 for r in rs),failures=[dict(attempt=r['attempt'],key=r['key'],exit=r['validation_exit'],errors=r['errors'],unsupported=r['unsupported_printed_axioms']) for r in rs if r['validation_exit']!=0])
(O/'EJS_summary.json').write_text(json.dumps(s,indent=2)+'\n');print(json.dumps(s))
