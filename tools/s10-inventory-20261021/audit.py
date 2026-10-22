#!/usr/bin/env python3
"""Focused integrity gates for the S10 reconciliation, including mutations."""
import copy,hashlib,importlib.util,json,resource,subprocess,sys,time
from pathlib import Path
P=Path(__file__).with_name('inventory.py')
spec=importlib.util.spec_from_file_location('s10_inventory',P);inv=importlib.util.module_from_spec(spec);spec.loader.exec_module(inv)
start=time.monotonic();base=inv.build();checks=[]
for name,value in base.items():
 assert (inv.E/name).read_bytes()==inv.encoded(value),'stale '+name
checks.append('deterministic JSON, frozen blob hashes, direct closures, targets, symbol aliases, model source/receipt/axioms')
original=inv.load

def reject(name,mutate):
 def load(file):
  value=original(file)
  if file==name:value=copy.deepcopy(value);mutate(value)
  return value
 inv.load=load
 try:
  inv.build()
 except AssertionError:
  checks.append('rejects '+name+' mutation')
 else:raise AssertionError('accepted corrupt '+name)
 finally:inv.load=original
reject('source-hashes.json',lambda x:x['files'][0].update(sha256='0'*64))
reject('elf-symbol-kinds.json',lambda x:x['artifacts']['default'].update(linked_sha256='0'*64))
def bad_target(x):
 row=next(f for f in x['declarations'] if any(c['target'] is not None for c in f['calls']))
 next(c for c in row['calls'] if c['target'] is not None)['target']=-1
reject('verifier-solana-cfg-v3.json',bad_target)
proposal=inv.proposal
try:
 def double(name,file=''):
  owners,boundary=proposal(name,file)
  if owners==['S1']:owners=['S1','S2']
  return owners,boundary
 inv.proposal=double;mutated=inv.build()['inventory.json']
 assert mutated['assigned_twice'] and mutated['counts']['assigned_twice']>base['inventory.json']['counts']['assigned_twice']
 checks.append('flags double cone ownership')
finally:inv.proposal=proposal
p=subprocess.run([sys.executable,'-B',str(P),'--check','--require-complete'],capture_output=True,text=True)
assert p.returncode==2,p.stdout+p.stderr
checks.append('complete release gate fails closed with exit 2')
r=resource.getrusage(resource.RUSAGE_SELF)
receipt=dict(schema='s10-reconciliation-integrity-receipt-v1',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=inv.R,text=True).strip(),command=[sys.executable,'-B',str(Path(__file__).resolve())],exit_status=0,wall_seconds=time.monotonic()-start,peak_rss_bytes=r.ru_maxrss if sys.platform=='darwin' else r.ru_maxrss*1024,swaps=r.ru_nswap,print_axioms='N/A: JSON validation; Lean audits retained separately',checks=checks,completeness_gate=dict(exit_status=p.returncode,stdout=p.stdout,meaning='EXPECTED FAILURE: frozen source reachability/refinement remains incomplete'),counts=base['inventory.json']['counts'],input_hashes=base['inventory.json']['input_hashes'],checker_sha256=hashlib.sha256(P.read_bytes()).hexdigest())
(inv.E/'validation.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
print(json.dumps(dict(exit_status=0,checks=len(checks),complete_gate=p.returncode,wall_seconds=receipt['wall_seconds'])))
