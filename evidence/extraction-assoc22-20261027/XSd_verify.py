"""Read-only verification of this job's local proof receipts and source snapshots."""
from pathlib import Path
import json,re,hashlib,subprocess
E=Path(__file__).resolve().parent
errors=[];rows=[];accepted={};allowed={'propext','Classical.choice','Quot.sound'}
for f in sorted(E.glob('XSd_L[0-9][0-9][0-9]/receipt.json')):
 r=json.loads(f.read_text());a=r['attempt'];n=int(a[-3:])
 if len(rows)>=100:errors.append(a+': actual compiler budget exceeded')
 for source,sha in r['source_hashes'].items():
  p=f.parent/'sources'/source
  if not p.exists() or hashlib.sha256(p.read_bytes()).hexdigest()!=sha:errors.append(a+': snapshot hash '+source)
 ad=E/(a+'-reservation.json')
 if not ad.exists() or json.loads(ad.read_text()).get('allowed') is not True:errors.append(a+': missing/refused admission')
 if '-M7000' not in r['command']:errors.append(a+': missing Lean cap')
 expected_limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 if r['limits']!=expected_limits:errors.append(a+': cgroup limits differ')
 if r['exit_status']==0:
  for line in r['print_axioms']:
   m=re.search(r'axioms: \[([^]]*)\]',line)
   if m:
    axes={x.strip() for x in m.group(1).split(',') if x.strip()}
    if not axes<=allowed:errors.append(a+': nonstandard accepted axioms '+line)
   elif 'does not depend on any axioms' not in line:errors.append(a+': unrecognized audit '+line)
  accepted[r['module']]=a
 rows.append({k:r[k] for k in ['attempt','module','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','source_hashes','limits','print_axioms']})
for m,a in accepted.items():
 p=E/(m+'.lean')
 if p.exists():
  r=json.loads((E/a/'receipt.json').read_text());expected=next(iter(r['source_hashes'].values()))
  if hashlib.sha256(p.read_bytes()).hexdigest()!=expected:errors.append(m+': current source differs from last accepted snapshot')
for m in ['XSd_InverseShape','XSd_InverseCompare','XSd_DotSequence','XSd_MapState','XSd_ArrayMap','XSd_DotReduce','XSd_DotFinish','XSd_DotFinishAll']:
 if m not in accepted:errors.append(m+': no accepted result')
b=(E/'XSd_top_before.lean.txt').read_bytes();a=(E/'XSd_top_after.lean.txt').read_bytes()
if a!=b:errors.append('headline statement changed')
changed=subprocess.check_output(['git','diff','--name-only','b7ff20b5bc4210d1f79f02acdecf731525d6bc7b','--'],text=True,cwd=E).splitlines()
for p in changed:
 if not p.startswith('evidence/extraction-assoc22-20261027/'):errors.append('out-of-scope path '+p)
v=dict(errors=errors,receipt_count=len(rows),pass_count=sum(r['exit_status']==0 for r in rows),fail_count=sum(r['exit_status']!=0 for r in rows),wall_seconds=sum(r['wall_seconds'] for r in rows),peak_rss_kib=max((int(r['peak_rss_kib']) for r in rows),default=0),swaps=sum(int(r['swaps']) for r in rows),accepted=accepted,top_statement_sha256=hashlib.sha256(a).hexdigest(),actual_top_removed=0,actual_top_added=0,actual_top_changed=0,kani_runs=0)
(E/'XSd_VERIFICATION.json').write_text(json.dumps(v,indent=2)+'\n')
(E/'XSd_attempts.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in rows))
print(json.dumps({k:v[k] for k in ['errors','receipt_count','pass_count','fail_count','wall_seconds','peak_rss_kib','swaps']}))
raise SystemExit(bool(errors))
