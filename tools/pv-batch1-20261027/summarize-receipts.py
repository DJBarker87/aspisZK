from pathlib import Path
import json,csv,hashlib,re,subprocess
E=Path('evidence/pv-batch1-20261027');t=json.loads((E/'TALLY.json').read_text())
lean=[]
for p in sorted((E/'lean-receipts').glob('*/receipt.json')):
 x=json.loads(p.read_text());x['receipt_path']=str(p.relative_to(E));lean.append(x)
charged=[r for r in lean if r['charged']];assert len(charged)==t['lean_charged']==100
assert len(t['used_ids'])==len(set(t['used_ids']))
manifest=json.loads((E/'audit-manifest.json').read_text())
coverage={}
for m,h in manifest['source_modules'].items():
 assert hashlib.sha256((E/'lean'/(m+'.lean')).read_bytes()).hexdigest()==h
 ok=[r for r in lean if r['module']==m and r['source_sha256']==h and r['exit']==0]
 assert ok,m
 coverage[m]=[r['attempt'] for r in ok]
audit=[];axioms=set()
for a in [53701,53702,53703]:
 x=next(r for r in lean if r['attempt']==a);assert x['exit']==0
 for line in x['print_axioms']:
  if 'depends on axioms:' in line:
   match=re.search(r'axioms: \[([^]]*)\]',line)
   assert match,line
   axioms.update(n.strip() for n in match[1].split(',') if n.strip())
 audit.append({k:x[k] for k in ['attempt','module','exit','wall_seconds','gnu_wall','peak_rss_kib','swap','source_revision','rust_source_revision','receipt_path']})
 audit[-1]['axiom_query_results']=len(x['print_axioms'])
assert axioms<={'propext','Classical.choice','Quot.sound'},axioms
assert audit[-1]['axiom_query_results']==728
rows=[]
for x in lean:
 rows.append(dict(kind='Lean',target=x['module'],exit=x['exit'],wall_seconds=x['wall_seconds'],gnu_wall=x['gnu_wall'],peak_rss_kib=x['peak_rss_kib'],swap=x['swap'],source_revision=x['source_revision'],rust_source_revision=x['rust_source_revision'],print_axioms='; '.join(x['print_axioms']) or 'none (failure before declarations)',receipt=x['receipt_path']))
for p in sorted(E.rglob('receipt.json')):
 if 'lean-receipts' in p.parts:continue
 x=json.loads(p.read_text())
 if 'command' not in x:continue
 rows.append(dict(kind='host build/extract/fixture',target=' '.join(map(str,x['command'])),exit=x.get('exit_status',x.get('exit')),wall_seconds=x.get('wall_seconds'),gnu_wall=x.get('gnu_wall',''),peak_rss_kib=x.get('peak_rss_kib'),swap=x.get('swaps',x.get('swap')),source_revision=x.get('source_revision'),rust_source_revision=x.get('source_revision'),print_axioms='N/A (no Lean)',receipt=str(p.relative_to(E))))
with (E/'receipts.csv').open('w') as f:
 w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
summary=dict(budget=t,charged_compile_count=len(charged),successful_compiles=sum(r['exit']==0 for r in charged),failed_compiles=[dict(attempt=r['attempt'],module=r['module'],exit=r['exit']) for r in charged if r['exit']!=0],max_peak_rss_kib=max(int(r['peak_rss_kib']) for r in charged),all_charged_swap_zero=all(str(r['swap'])=='0' for r in charged),accepted_axioms=sorted(axioms),audits=audit,final_source_coverage=coverage,formal_target_established=False,headline_premises_removed=0,stop_reason='100/100 Lean attempts exhausted; final audits passed',unlaunched_reserved_ids=dict(ids=[53897,53898,53899],charged=0,reason='source-exists assertion before Lean/reservation; consumed permanently'))
(E/'FINAL-AUDIT.json').write_text(json.dumps(summary,indent=2)+'\n')
t.update(stopped='Lean budget exhausted:100/100; final audits passed; target not established',stage='complete handoff',audit_ids=[53701,53702,53703]);(E/'TALLY.json').write_text(json.dumps(t,indent=2)+'\n')
print(json.dumps({k:summary[k] for k in ['charged_compile_count','successful_compiles','max_peak_rss_kib','all_charged_swap_zero','accepted_axioms','audits']},indent=2))
