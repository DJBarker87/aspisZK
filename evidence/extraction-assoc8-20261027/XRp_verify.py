from pathlib import Path
import json,hashlib,re
E=Path(__file__).resolve().parent
allowed={'propext','Classical.choice','Quot.sound'}
receipts=sorted((json.loads(p.read_text()) for p in E.glob('XRp_L*/receipt.json')),key=lambda r:r['attempt'])
errors=[];audited={};success=[]
for r in receipts:
 a=r['attempt'];d=E/a
 for n in ['module','source_revision','source_hashes','deps_fingerprint','command','exit_status','wall_seconds','peak_rss_kib','swaps','limits','print_axioms']:
  if n not in r:errors.append(a+' missing '+n)
 if r['limits']!={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}:errors.append(a+' limits')
 if str(r['swaps'])!='0':errors.append(a+' swaps')
 for src,sha in r['source_hashes'].items():
  if hashlib.sha256((d/'sources'/src).read_bytes()).hexdigest()!=sha:errors.append(a+' source mismatch')
 if r['exit_status']==0:
  success.append(r)
  for line in r['print_axioms']:
   if 'does not depend on any axioms' in line:continue
   axioms=set(x.strip() for x in re.search(r'\[([^]]*)\]',line,re.S).group(1).split(','))
   if not axioms<=allowed:errors.append(a+' nonstandard '+line)
 for n in ['XRp_L099','XRp_L100','XRp_L101']:
  if a==n:
   if r['exit_status']:errors.append(a+' audit failed')
   for line in r['print_axioms']:audited[re.search(r"'([^']+)'",line).group(1)]=line
plan=json.loads((E/'XRp_FINAL_AUDIT_PLAN.json').read_text())
for group in plan:
 for name in group['theorems']:
  if name not in audited:errors.append('missing theorem audit '+name)
 for module in group['proof_modules']:
  sha=hashlib.sha256((E/(module+'.lean')).read_bytes()).hexdigest()
  matches=[r for r in success if r['module']==module and sha in r['source_hashes'].values()]
  if not matches:errors.append('current proof not checked '+module)
if len(receipts)!=100:errors.append('budget count '+str(len(receipts)))
if (E/'XRp_top_before.lean.txt').read_bytes()!=(E/'XRp_top_after.lean.txt').read_bytes():errors.append('top changed')
summary={'lean_used':len(receipts),'lean_limit':100,'pass':len(success),'fail':len(receipts)-len(success),'kani_used':0,'kani_limit':10,'compiler_wall_seconds':sum(r['wall_seconds'] for r in receipts),'max_peak_rss_kib':max(int(r['peak_rss_kib']) for r in receipts),'swaps':0,'new_theorems_audited':len(audited),'proof_modules':sum(len(g['proof_modules']) for g in plan),'memory_failed':['XRp_L091','XRp_L095'],'precompiler_only':['XRp_L043'],'root_audit':'deferred','errors':errors}
(E/'XRp_VERIFICATION.json').write_text(json.dumps(summary,indent=2)+'\n')
(E/'XRp_BUDGET.json').write_text(json.dumps({**summary,'status':'EXHAUSTED: no further compiler/prover runs'},indent=2)+'\n')
(E/'XRp_ACCEPTED_AXIOMS.json').write_text(json.dumps(audited,indent=2)+'\n')
with (E/'XRp_attempts.jsonl').open('w') as f:
 for r in receipts:f.write(json.dumps(r,separators=(',',':'))+'\n')
print(json.dumps(summary,indent=2))
if errors:raise SystemExit(1)
