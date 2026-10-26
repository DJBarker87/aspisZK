from pathlib import Path
import hashlib,json,re,subprocess
E=Path(__file__).resolve().parent;R=E.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
receipts=[];passing={};preflights=[]
for n in range(1,101):
 a=f'FIp_{n:03}';p=E/a/'receipt.json'
 if p.exists():
  d=json.loads(p.read_text());receipts.append(d)
  assert d['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},a
  assert '-M7000' in d['command'],a
  if d['exit_status']==0:
   assert all('sorryAx' not in s for s in d['print_axioms']),a
   for line in d['print_axioms']:
    if 'depends on axioms: [' in line:
     used=set(line.split('depends on axioms: [',1)[1].split(']',1)[0].split(', '));assert used<= {'propext','Classical.choice','Quot.sound'},(a,line)
   for s,h in d['source_hashes'].items():passing.setdefault((s,h),[]).append(a)
 else:
  p=E/(a+'-preflight.json');assert p.exists(),a
  preflights.append(json.loads(p.read_text()))
sources=[]
for p in sorted((R/'lean').glob('FIp_*.lean')):
 s=p.read_text()
 assert not re.search(r'\b(sorry|admit|native_decide)\b|(?m:^axiom )|(?m:^set_option max(?:Heartbeats|RecDepth))',s),str(p)
 matches=passing.get((p.name,sha(p)),[])
 assert matches,('No successful current-source receipt',str(p),sha(p))
 sources.append(dict(source=str(p.relative_to(R)),sha256=sha(p),passing=matches))
report=dict(charged_lean_ids=100,compiler_starts=len(receipts),preflight_charges=len(preflights),kani_runs=0,kani_limit=30,lean_limit=100,
 sources=sources,preflights=preflights,
 receipts=[{k:d.get(k) for k in ['attempt','sources','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','source_hashes','print_axioms','cgroup','limits']} for d in receipts],
 scope='Focused new modules in pinned coherent SInt2 workspace; unchanged cached dependencies reused. No package/frozen manifest replay or coherent release rebuild claimed.')
(E/'FIp_validation.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(dict(charged=100,starts=len(receipts),preflight=len(preflights),sources=len(sources),unmatched=0),indent=2))
