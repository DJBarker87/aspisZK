#!/usr/bin/env python3
import pathlib,json,hashlib,re,subprocess
root=pathlib.Path(__file__).resolve().parents[2];e=root/'evidence/s2z-20261023'
rows=[]
for p in sorted(e.glob('lean-*/receipt.json')):
 r=json.loads(p.read_text());rows.append(r)
 for name,sha in r['source_hashes'].items():
  assert hashlib.sha256((p.parent/'sources'/name).read_bytes()).hexdigest()==sha
 if r['exit_status']==0:
  assert r['print_axioms']
  for line in r['print_axioms']:
   m=re.search(r'depends on axioms: \[([^]]*)\]',line)
   if m: assert set(re.findall(r'[A-Za-z_.]+',m[1])) <= {'propext','Classical.choice','Quot.sound'},line
  assert r['swaps']=='0'
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
latest={name:r for r in rows for name in r['source_hashes']}
for name,r in latest.items():
 current=root/'docs/research/100bit-spend-path-20261013/lean'/name
 assert hashlib.sha256(current.read_bytes()).hexdigest()==r['source_hashes'][name]
 assert r['exit_status']==0,(name,r['attempt'])
x={'schema':'focused-extractor-proof-packet-v1','branch':subprocess.check_output(['git','branch','--show-current'],cwd=root,text=True).strip(),'audit_source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),'lean_attempts':len(rows),'kani_runs':0,'attempts':rows,'final_sources':{n:r['attempt'] for n,r in latest.items()},'scope':'Focused cached module checks, not a coherent frozen release rebuild','remaining':'Native backend interpretation, child event/reachability reification, and same-account transaction history'}
(e/'manifest.json').write_text(json.dumps(x,indent=2)+'\n')
print(f'Audit passed: Lean {len(rows)}/100, Kani 0/60')
