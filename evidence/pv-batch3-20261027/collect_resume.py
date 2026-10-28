"""Validate retained resume receipts and bind current accepted sources."""
from pathlib import Path
import json,hashlib,re,subprocess
D=Path(__file__).resolve().parent;L=D/'lean';t=json.loads((D/'TALLY-resume.json').read_text());records=[];current={};bad=[]
for a in t['used_ids']:
 R=D/'receipts'/f'lean-{a}';p=R/'receipt/receipt.json'
 if not p.exists():
  records.append({'attempt':a,'charged':False,'receipt':str(R.relative_to(D))});continue
 r=json.loads(p.read_text());sub=json.loads((R/'submission.json').read_text());snap=R/'source.lean'
 assert hashlib.sha256(snap.read_bytes()).hexdigest()==sub['source_sha256'],a
 assert r['limits']['memory.swap.max']=='0' and int(r['limits']['memory.max'])<=8*2**30,a
 log=(R/'receipt/stdout.log').read_text()+(R/'receipt/stderr.log').read_text()
 ax=[x for x in log.splitlines() if 'depends on axioms:' in x or 'does not depend on any axioms' in x]
 if r['exit_status']==0:
  for x in ax:
   if 'depends on axioms:' in x:
    names=re.findall(r'\[([^]]*)\]',x)
    if names and set(n.strip() for n in names[-1].split(',')) - {'propext','Classical.choice','Quot.sound'}:bad.append({'attempt':a,'axioms':x})
 rec={'attempt':a,'module':sub['module'],'charged':True,'exit':r['exit_status'],'wall_seconds':r['wall_seconds'],'peak_rss_kib':r['peak_rss_kib'],'swap':r['swaps'],'cgroup_peak_bytes':r.get('cgroup_memory_peak_bytes'),'source_revision':r['source_revision'],'source_sha256':sub['source_sha256'],'print_axioms':ax,'receipt':str(p.relative_to(D))};records.append(rec)
 q=L/(sub['module']+'.lean')
 if r['exit_status']==0 and q.exists() and hashlib.sha256(q.read_bytes()).hexdigest()==sub['source_sha256']:current[sub['module']]=rec
assert not bad,bad
assert sum(r['charged'] for r in records)==t['lean_attempts']
(D/'resume-receipt-index.json').write_text(json.dumps({'charged':t['lean_attempts'],'ids_consumed':len(t['used_ids']),'kani':0,'receipts':records,'axiom_violations':bad},indent=2)+'\n')
(D/'resume-current-source-coverage.json').write_text(json.dumps({'revision':subprocess.check_output(['git','rev-parse','HEAD']).decode().strip(),'modules':current},indent=2)+'\n')
print({'charged':t['lean_attempts'],'consumed_ids':len(t['used_ids']),'accepted':sum(r.get('exit')==0 for r in records if r['charged']),'rejected':sum(r.get('exit')!=0 for r in records if r['charged']),'current_modules':len(current),'max_peak_rss_kib':max(r.get('peak_rss_kib',0) for r in records),'axiom_violations':bad})
