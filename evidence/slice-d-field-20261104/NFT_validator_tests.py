"""Supplemental adversarial admission checks; no new prover/release run."""
import importlib.util,pathlib,json,copy
from unittest.mock import patch
E=pathlib.Path(__file__).resolve().parent
sp=importlib.util.spec_from_file_location('NFT_guards',E/'NFT_certify.py');m=importlib.util.module_from_spec(sp);sp.loader.exec_module(m)
original=m.J;tests=[]
def reject(label,action):
 try:action()
 except(AssertionError,ValueError):tests.append(label)
 else:raise AssertionError('accepted '+label)
for label,name,edit in [
 ('graph drift','NFT_K040-graph-check.json',lambda x:x.update(graph_matches_frozen=False)),
 ('lock drift','NFT_K040-lock-check.json',lambda x:x.update(after='0'*64)),
 ('source drift','NFT_K040-source-check.json',lambda x:x.update(errors=['body drift'])),
 ('admission denied','NFT_K040-admission.json',lambda x:x['reservation'].update(allowed=False)),
 ('admission exit78','NFT_K040-admission.json',lambda x:x.update(exit=78)),
 ('swap allowed','NFT_K040/receipt.json',lambda x:x['limits'].update({'memory.swap.max':'1'})),
 ('online Cargo','NFT_K040/receipt.json',lambda x:x['env'].update(CARGO_NET_OFFLINE='false')),
 ('debug profile','NFT_K040/receipt.json',lambda x:x['env'].update(CARGO_PROFILE_DEV_OPT_LEVEL='0'))]:
 def modified(n):
  x=copy.deepcopy(original(n))
  if n==name:edit(x)
  return x
 with patch.object(m,'J',modified):reject(label,lambda:m.native(40,0))
for k in [5,56,69]:reject('excluded native '+str(k),lambda:m.native(k,0))
def modified(n):
 x=copy.deepcopy(original(n))
 if n=='NFT_K039/receipt.json':x['env']['RUSTFLAGS']+=' --cfg drift'
 return x
with patch.object(m,'J',modified):reject('copy configuration mismatch',lambda:m.copy_pair(38,39))
assert len(m.J('NFT_CLOSED.json')['functions'])==11
assert len(m.J('NFT_LEDGER_DELTA.json')['new_closed_rows'])==12
(E/'NFT_VALIDATOR_TESTS.json').write_text(json.dumps(dict(status='PASS',checks=tests),indent=1)+'\n');print('PASS',len(tests),'admission guards')
