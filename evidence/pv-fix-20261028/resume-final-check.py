from pathlib import Path
import json,hashlib,re
D=Path('/home/dombarker/project-offloads/codex-pv-fix-20261028');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
pre=json.loads((D/'preflight.json').read_text())['rdcd'];records={r['module']:r for r in pre['projects']};ext={r['module']:r for r in pre['external']};pins=json.loads((D/'resume-source-pins.json').read_text());rows=[]
for p in sorted(D.glob('receipt-621*.json')):
 r=json.loads(p.read_text());a=r['attempt'];assert 62100<=a<=62199 and r['compiler_launched']
 ad=json.loads((D/f'admission-{a}.json').read_text());bar=json.loads((D/f'barrier-{a}.json').read_text());assert ad['allowed'] is True and bar['allowed'] is True and r['admission_exit']==0
 assert bar['own_limits']=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0','pids.max':'64'}
 src=D/'rdcd/sources'/(r['module']+'.lean');assert sha(src)==pins[r['module']]['sha256']==r['source']['sha256']
 assert r['environment_sha256']==sha(D/f'env-{a}.json')==sha(D/'resume-env.json')
 if r['exit']==0:assert sha(D/'rdcd/objects'/(r['module']+'.olean'))==r['object_sha256']
 o=(D/f'out-{a}.log').read_text();lines=o.splitlines();blocks=[]
 for i,l in enumerate(lines):
  if 'depends on axioms:' not in l:continue
  block=l;j=i+1
  while ']' not in block and j<len(lines):block+='\n'+lines[j];j+=1
  names=re.sub(r'\.\{[^}]*\}','',block.split('depends on axioms:',1)[1]).strip('[] \n').split(',')
  assert all(x.strip() in ['propext','Classical.choice','Quot.sound'] for x in names if x.strip()),block
  blocks.append(block)
 r['axioms_full']=blocks;r['axioms_result']='; '.join(blocks) if blocks else 'No emitted #print axioms in unchanged target.'
 rows.append(r)
assert len(rows)<=40 and len({r['attempt'] for r in rows})==len(rows)
latest={r['module']:r for p in sorted(D.glob('receipt-*.json')) if (r:=json.loads(p.read_text())).get('exit')==0 and r['cohort']=='rdcd'};safe=json.loads((D/'resume-cache-check.json').read_text());visited={}
def visit(n):
 if n in visited:return visited[n]['object_sha256']
 if n in ext:
  p=D/'external-objects'/(n+'.olean');assert sha(p)==ext[n]['object_sha256'];return ext[n]['object_sha256']
 r=records[n];s=Path(r['source']);assert sha(s)==r['source_sha256'];fr=latest.get(n);expected=fr['object_sha256'] if fr else r['object_sha256'];p=D/'rdcd/objects'/(n+'.olean');assert p.is_file() and sha(p)==expected
 deps={j['module']:j['object_sha256'] for j in r['imports']}
 if fr:
  for c,v in fr['dependencies'].items():
   if c in deps:deps[c]=v['object_sha256']
 else:assert n in safe
 for c,h in deps.items():assert visit(c)==h,(n,c)
 visited[n]=dict(source_sha256=sha(s),source_blob=r['source_blob'],object_sha256=expected,imports=deps,receipt=fr['attempt'] if fr else 'verified inherited cache');return expected
for r in rows:
 if r['exit']==0 and r['module'] in records:visit(r['module'])
for n in ['R1Z/PV_CB_Op109CanonicalBinding','R1Z/PV_CB_Op109Funs','R1Z/PV_CB_Op109Exact','R1Z/PV_RDCD_Op109Audit']:visit(n)
audit=next(r for r in rows if r['module']=='R1Z/PV_FIX_V213Audit');assert audit['exit']==0 and len(audit['axioms_full'])==3
for n,j in audit['dependencies'].items():assert visit(n)==j['object_sha256']
missing=[n for n in json.loads((D/'resume-execution-order.json').read_text()) if n not in latest]
summary=dict(status='OPEN' if missing else 'RESTORED',lean_attempts=len(rows),passed=sum(r['exit']==0 for r in rows),failed=sum(r['exit']!=0 for r in rows),native_scopes=0,kani=0,refusals=len(list(D.glob('refusal-621*.json'))),new_ruling_t_violations=[],focused_statement_axioms_audit=audit['attempt'],restoring_theorem='R1Z.PV_RDCD_Op109Audit.source',remaining=missing,verified_project_count=len(visited),peak_rss_kib=max(r['peak_rss_kib'] for r in rows),all_swaps_zero=all(r['swap']==0 for r in rows))
for name,v in [('resume-attempts.json',rows),('resume-final-fingerprint.json',visited),('resume-summary.json',summary)]: (D/name).write_text(json.dumps(v,indent=2)+'\n')
print(json.dumps(summary,indent=2))
