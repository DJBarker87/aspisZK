"""Validate continuation receipts, own-root audits and committed source snapshots."""
from pathlib import Path
import json,re,hashlib,lzma
E=Path(__file__).resolve().parent
standard={'propext','Classical.choice','Quot.sound'}
def sha(b):return hashlib.sha256(b).hexdigest()
rows=[]
for p in sorted(E.glob('LIB_L[0-9][0-9][0-9]/receipt.json')):
 if int(p.parent.name[-3:])<182:continue
 x=json.loads(p.read_text());assert x['exit_status']==0,(p,x['exit_status'])
 admission=json.loads((E/(x['attempt']+'-admission.json')).read_text());assert admission['exit']==0 and admission['reservation']['allowed'] is True
 disk=json.loads((E/(x['attempt']+'-disk-0.json')).read_text());assert disk['free']>=40_000_000_000
 assert str(x['swaps'])=='0'
 assert x['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 shares=[json.loads(line) for line in (E/'LIB_ATTEMPTS.jsonl').read_text().splitlines() if line.strip()]
 assert any(z.get('attempt')==x['attempt'] and z.get('event')=='share_check' and z['host']['count']<6 for z in shares)
 for line in x['print_axioms']:
  m=re.search(r'depends on axioms: \[(.*?)\]',line)
  if m:assert set(m[1].split(', '))<=standard,line
 if x['kind']=='lean':
  module=x['module'];src=E/(module+'.lean')
  if not src.exists():src=E/'LIB_dependency_inputs'/(module+'.lean')
  for name,h in x['source_hashes'].items():
   snapshot=p.parent/'sources'/name
   assert snapshot.exists() and sha(snapshot.read_bytes())==h,(module,name)
  x['current_source']=sha(src.read_bytes()) in x['source_hashes'].values()
 row={k:x[k]for k in ['attempt','module','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','source_hashes','print_axioms','limits']}
 row['current_source']=x.get('current_source')
 rows.append(row)
assert all(any(x['module']==m and x['current_source'] for x in rows) for m in ['LIB_VLib','LIB_Prepared','LIB_S1','LIB_Instances','LIB_BUNDLE_IMPORT','LIB_VLibR4'])
roots=json.loads((E/'LIB_BUNDLE_ROOTS.json').read_text());audited={};groups=[]
for g in roots['groups']:
 p=E/'LIB_audit'/('proof'+str(g))/('proof'+str(g)+'.json');x=json.loads(p.read_text());assert x['validated']
 for row in x['results']:
  assert row['equal'] and set(row['walked_axioms'])<=standard
  assert row['root'] not in audited;audited[row['root']]=row
 groups.append(dict(group=g,roots=len(x['results']),receipt=str(p.relative_to(E)),sha256=sha(p.read_bytes())))
assert set(audited)==set(roots['roots'])
prints={}
for x in rows:
 for line in x['print_axioms']:
  m=re.match("'([^']+)' (?:depends on axioms|does not depend on any axioms)",line)
  if m:prints[m[1]]=line
assert set(roots['roots'])<=set(prints)
for root in roots['roots']:
 line=prints[root];m=re.search(r'depends on axioms: \[(.*?)\]',line);expected=set(m[1].split(', ')) if m else set()
 assert expected==set(audited[root]['walked_axioms']),root
for p in E.glob('LIB_NEP_*_REACHABLE.txt.xz'):
 if not any(root in p.name for root in roots['roots']):continue
 assert sha(lzma.decompress(p.read_bytes()))==Path(str(p)[:-3]+'.sha256').read_text().strip(),p
summary=dict(target_established=False,continuation_budget=162,scopes_used=len(rows),prior_used=88,resumed_total=88+len(rows),kani=0,extraction=0,all_exit0=True,standard_axioms_only=True,own_roots=len(audited),print_and_raw_agree=True,collector_agrees=True,raw_groups=groups,max_peak_rss_kib=max(int(x['peak_rss_kib']) for x in rows),wall_seconds=sum(x['wall_seconds']for x in rows),swaps=0,rows=rows)
assert len(rows)<=162
(E/'LIB_BUNDLE_VALIDATION.json').write_text(json.dumps(summary,indent=2)+'\n')
(E/'LIB_BUNDLE_TRANSCRIPT.tsv').write_text('attempt\ttarget\texit\twall_s\tpeak_rss_KiB\tswap\trevision\n'+''.join('\t'.join(str(x[k]) for k in ['attempt','module','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision'])+'\n'for x in rows))
(E/'LIB_BUNDLE_AUDIT_SUMMARY.json').write_text(json.dumps(dict(roots=roots['roots'],groups=groups,standard_only=True,collector_agrees=True,print_and_raw_agree=True),indent=2)+'\n')
print(json.dumps({k:v for k,v in summary.items()if k not in ['rows','raw_groups']}))
