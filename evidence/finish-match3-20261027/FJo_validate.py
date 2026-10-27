from pathlib import Path
import hashlib,json,re,subprocess
P=Path(__file__).resolve().parent;R=P.parents[1]
receipts=[];passed={};preflights=[]
for n in range(1,101):
 a=f'FJo_{n:03}';p=P/a/'receipt.json'
 if p.exists():
  j=json.loads(p.read_text());receipts.append(j)
  if j['exit_status']==0:
   assert j['swaps']=='0' or j['swaps']==0
   for s in (p.parent/'sources').glob('FJo_*.lean'):
    passed[hashlib.sha256(s.read_bytes()).hexdigest()]=dict(attempt=a,module=s.stem)
 elif (P/(a+'-preflight.json')).exists():preflights.append(json.loads((P/(a+'-preflight.json')).read_text()))
delivered=[];missing=[]
for p in sorted((R/'lean').glob('FJo_*.lean')):
 sha=hashlib.sha256(p.read_bytes()).hexdigest()
 s=p.read_text()
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b|set_option\s+(maxRecDepth|maxHeartbeats)',s),p
 row=dict(module=p.stem,sha256=sha)
 if sha in passed:row.update(passed[sha]);delivered.append(row)
 else:missing.append(row)
axioms=[]
for j in receipts:
 if j['exit_status']==0:
  for line in j['print_axioms']:
   if 'depends on axioms:' in line:
    found=line.split('depends on axioms:')[1]
    names=set(re.findall(r'[A-Za-z_.]+',found))
    assert names<=set(['propext','Classical.choice','Quot.sound']),(j['attempt'],line)
   axioms.append(dict(attempt=j['attempt'],line=line))
out=dict(charged=len(receipts)+len(preflights),compiler_starts=len(receipts),passes=sum(j['exit_status']==0 for j in receipts),failures=sum(j['exit_status']!=0 for j in receipts),preflights=preflights,kani_runs=0,delivered=delivered,missing=missing,successful_axiom_reports=axioms,limits=dict(Lean='-M7000',MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64,one_own_scope_at_a_time=True),root_sha256=hashlib.sha256((R/'lean/ARX_Root.lean').read_bytes()).hexdigest())
(P/'FJo_validation.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:out[k] for k in ['charged','compiler_starts','passes','failures','missing']},indent=2))
assert not missing,missing
assert out['charged']==100,out['charged']
