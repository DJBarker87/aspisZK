#!/usr/bin/env python3
"""Static final packet audit, without a prover or release-closure claim."""
from pathlib import Path
import json,hashlib,re,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/port4c-20261023';L=R/'docs/research/100bit-spend-path-20261013/lean'
receipts=[json.loads(p.read_text()) for p in sorted(E.glob('lean-*/receipt.json'))]
assert len(receipts)<=100
accepted={}
for r in receipts:
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},r['attempt']
 assert r['swaps']=='0',r['attempt']
 for f,h in r['source_hashes'].items():
  assert hashlib.sha256((E/r['attempt']/'sources'/f).read_bytes()).hexdigest()==h
 if r['exit_status']==0:
  for line in r['print_axioms']:
   assert 'sorryAx' not in line,line
   if 'depends on axioms:' in line:
    axioms=re.search(r'\[([^\]]*)\]',line).group(1).split(',')
    assert set(a.strip() for a in axioms)<={'propext','Classical.choice','Quot.sound'},line
  for f,h in r['source_hashes'].items():accepted[(f,h)]=r['attempt']
modules=[]
for p in sorted(L.glob('Port4C_*.lean')):
 s=p.read_text();sha=hashlib.sha256(p.read_bytes()).hexdigest()
 assert not re.search(r'\b(sorry|axiom|admit|native_decide)\b',re.sub(r'/\-.*?\-/|--[^\n]*','',s,flags=re.S)),p
 assert not re.search(r'set_option\s+(maxRecDepth|maxHeartbeats)',s),p
 assert (p.name,sha) in accepted,('Missing accepted CURRENT source receipt',p)
 modules.append({'module':p.stem,'sha256':sha,'accepted_attempt':accepted[p.name,sha]})
base='986dc0bd7d'
changed=subprocess.check_output(['git','diff','--name-only',base],cwd=R,text=True).splitlines()
for f in changed:
 assert f.startswith(('evidence/port4c-20261023/','tools/port4c-20261023/','docs/research/100bit-spend-path-20261013/lean/Port4C_')),f
protected=['crates/aspis-r1-cost-probe/src/verifier.rs','crates/aspis-r1-cost-probe/src/candidate.rs','crates/aspis-core/src/field.rs','programs/r1-cost-probe/src/r1_pool_adapter.rs','Cargo.lock']
pins=[]
for f in protected:
 historical=subprocess.check_output(['git','show',base+':'+f],cwd=R)
 current=(R/f).read_bytes();assert current==historical,f
 pins.append({'path':f,'sha256':hashlib.sha256(current).hexdigest(),'base':base})
reserved=[p.stem for p in (R/'tools/port4c-20261023').glob('lean-*.json') if not (E/p.stem/'receipt.json').exists()]
report={'qualification':'Focused development proof packet; S2/frozen2 full query/model closure and deployed soundness remain OPEN; no full frozen manifest replay','actual_lean_compiles':len(receipts),'lean_budget':100,'kani_runs':0,'kani_budget':60,'reserved_without_compile':sorted(reserved),'accepted_current_modules':modules,'protected_source_pins':pins,'inherited_elf_pins_only':['f8c0ec72…','63ad3e9c…','121f3e29…'],'elf_rebuild':'Not required: no shipped-source changes; no new ELF certification claimed','source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),'excluded_failed_attempts':[r['attempt'] for r in receipts if r['exit_status']!=0]}
(E/'audit.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'modules':len(modules),'actual_lean_compiles':len(receipts),'reserved_without_compile':sorted(reserved),'protected_source_pins':'unchanged'}))
