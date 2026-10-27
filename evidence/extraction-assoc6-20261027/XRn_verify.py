from pathlib import Path
import json,hashlib,re
E=Path(__file__).resolve().parent
errors=[];groups={};accepted_axioms=[]
for kind in ['L','K']:
 receipts=[]
 for p in sorted(E.glob('XRn_'+kind+'*/receipt.json')):
  r=json.loads(p.read_text());receipts.append(r)
  for src,expected in r['source_hashes'].items():
   snapshot=p.parent/'sources'/src
   if not snapshot.exists() or hashlib.sha256(snapshot.read_bytes()).hexdigest()!=expected:errors.append(str(snapshot)+' source hash')
  for k,v in {'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}.items():
   if str(r['limits'][k])!=v:errors.append(r['attempt']+' cap '+k)
  if int(r['swaps'])!=0:errors.append(r['attempt']+' swap')
  if kind=='L':
   if '-M7000' not in r['command'] or '-j1' not in r['command']:errors.append(r['attempt']+' Lean flags')
   if r['exit_status']==0:
    for report in r['print_axioms']:
     for block in re.findall(r'\[([^\]]*)\]',report,re.S):
      axioms={x.strip() for x in block.split(',') if x.strip()}
      if not axioms<={'propext','Classical.choice','Quot.sound'}:errors.append(r['attempt']+' nonstandard '+report)
     accepted_axioms.append(dict(attempt=r['attempt'],report=report))
 groups[kind]=dict(invocations=len(receipts),passed=sum(r['exit_status']==0 for r in receipts),failed=sum(r['exit_status']!=0 for r in receipts),wall_seconds=sum(r['wall_seconds'] for r in receipts),peak_rss_kib=max(int(r['peak_rss_kib']) for r in receipts),swaps=sum(int(r['swaps']) for r in receipts))
assert groups['L']['invocations']==100,groups
assert groups['K']['invocations']==10,groups
for n in ['XRn_L072','XRn_L073']:
 if (E/n/'receipt.json').exists():errors.append(n+' unexpectedly compiled')
before=(E/'XRn_top_before.lean.txt').read_bytes();after=(E/'XRn_top_after.lean.txt').read_bytes()
if before!=after:errors.append('actual-top source changed')
for item in json.loads((E/'XRn_join_plan.json').read_text()):
 if hashlib.sha256((E/(item['module']+'.lean')).read_bytes()).hexdigest()!=item['sha256']:errors.append(item['module']+' transform hash')
for a in ['XRn_L101','XRn_L102']:
 if json.loads((E/a/'receipt.json').read_text())['exit_status']!=0:errors.append(a+' final audit')
(E/'XRn_ACCEPTED_AXIOMS.json').write_text(json.dumps(accepted_axioms,indent=2)+'\n')
result=dict(budget=groups,preflight_only=['XRn_L072','XRn_L073'],axiom_reports=len(accepted_axioms),actual_top_sha256=hashlib.sha256(before).hexdigest(),errors=errors)
(E/'XRn_VERIFICATION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2));assert not errors
