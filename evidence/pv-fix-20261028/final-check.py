from pathlib import Path
import json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-fix-20261028');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();rows=[]
pre=json.loads((D/'preflight.json').read_text())
for p in sorted(D.glob('receipt-*.json')):
 r=json.loads(p.read_text());a=r['attempt'];assert 62000<=a<=62099
 ad=json.loads((D/f'admission-{a}.json').read_text());bar=json.loads((D/f'barrier-{a}.json').read_text());assert ad['allowed'] is True and bar['allowed'] is True and r['admission_exit']==0
 assert bar['own_limits']=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0','pids.max':'64'}
 src=D/r['cohort']/'sources'/(r['module']+'.lean');assert sha(src)==r['source']['sha256']
 if r['exit']==0:assert sha(D/r['cohort']/'objects'/(r['module']+'.olean'))==r['object_sha256']
 o=(D/f'out-{a}.log').read_text();lines=o.splitlines();axioms=[]
 for i,l in enumerate(lines):
  if 'depends on axioms:' in l:
   block=l;j=i+1
   while ']' not in block and j<len(lines):block+='\n'+lines[j];j+=1
   assert 'sorryAx' not in block;axioms.append(block)
 r['axioms_full']=axioms;r['axioms_result']='; '.join(axioms) if axioms else ('No #print axioms output: unchanged target has no audit directive.' if r['exit']==0 else 'No axioms result: compiler failed before theorem audit.')
 rows.append(r)
assert len(rows)==15 and {r['attempt'] for r in rows}==set(range(62000,62015))
(D/'attempts.json').write_text(json.dumps(rows,indent=2)+'\n')
# Preserve the exact effective environment content used by each attempt.
for r in rows:
 cohort=r['cohort'];env=pre[cohort]['original_environment'].copy()
 if r['attempt']<=62001:env=pre[cohort]['environment']
 elif r['attempt']>=62004:env['LEAN_PATH']=str(D/'external-objects')+':'+env['LEAN_PATH']
 b=(json.dumps(env,indent=2)+'\n').encode();assert hashlib.sha256(b).hexdigest()==r['environment_sha256'],r['attempt']
 (D/f'env-{r["attempt"]}.json').write_bytes(b)
# The dedicated audit is deliberately NOT represented as having run.
order=json.loads((D/'affected-order.json').read_text());success={r['module']:r for r in rows if r['exit']==0};statuses=[]
for r in order:
 m=r['module'];fresh=success.get(m);statuses.append(dict(module=m,source_blob=r['blob'],source_sha256=r['sha256'],fresh_attempt=fresh['attempt'] if fresh else None,status='FRESH' if fresh else 'OPEN — no fresh object',imports=r['imports']))
missing=[]
for r in pre['rdcd']['projects']:
 p=D/'rdcd/objects'/(r['module'].replace('.','/')+'.olean')
 if not p.is_file():missing.append(dict(module=r['module'],source_blob=r['source_blob'],expected_object_sha256=r['object_sha256']))
summary=dict(lean_attempts=len(rows),passed=sum(r['exit']==0 for r in rows),failed=sum(r['exit']!=0 for r in rows),native_scopes=0,kani=0,refusals=len(list(D.glob('refusal-*.json'))),new_ruling_t_violations=[],replay=dict(status='PASSED',attempt=62002,initial_input_failures=[62000,62001],single_invocation_requirement_met=False),v213=dict(status='OPEN',binding_fresh_attempt=62012,affected=statuses,focused_restoring_statement_axioms_audit='NOT RUN — missing PV_RDCD_Op109Audit and exhausted budget',missing_private_objects=missing),peak_rss_kib=max(r['peak_rss_kib'] for r in rows),all_swaps_zero=all(r['swap']==0 for r in rows))
(D/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps({k:v for k,v in summary.items() if k not in ['v213']},indent=2))
