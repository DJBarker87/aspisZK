"""Canonical-owner replay of fresh registry body; no body replacement or axiom templates."""
from pathlib import Path
import re,json,hashlib
E=Path(__file__).resolve().parent
raw=E/'NND_registry/raw/NND_registry/Funs.lean'
t=raw.read_text();m=re.search(r'^def r1_pool_adapter\.owned\.authenticate_invariant_release_registry\n',t,re.M);assert m
body=t[m.start():].rsplit('end NND_registry',1)[0].strip()
name='r1_pool_adapter.owned.authenticate_invariant_release_registry'
body=body.replace('def '+name+'\n','def fresh (ops : Ops)\n',1)
adapter=json.loads(Path('docs/research/100bit-spend-path-20261013/lean/AdapterRw-emission-adapter.json').read_text())
changes=[]
for symbol,slot in sorted(adapter['boundaries'].items(),key=lambda x:-len(x[0])):
 pattern=r'(?<![\w.])'+re.escape(symbol)+r'(?![\w.])'
 body,n=re.subn(pattern,'ops.'+slot,body)
 if n:changes.append(dict(symbol=symbol,replacement='ops.'+slot,count=n))
for symbol in ['r1_pool_adapter.owned.require_readonly_account','r1_pool_adapter.owned.OwnedAccount.data','solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey']:
 pattern=r'(?<![\w.])'+re.escape(symbol)+r'(?![\w.])'
 body,n=re.subn(pattern,'('+symbol+' ops)',body)
 if n:changes.append(dict(symbol=symbol,replacement='('+symbol+' ops)',count=n))
# Aeneas clips nesting indentation at column 68. Re-layout ONLY after full
# punctuation/identifier token equality with the coherent canonical layout.
canonical=Path('docs/research/100bit-spend-path-20261013/lean/AdapterRwModel.lean').read_text()
canonical=canonical.split('def '+name,1)[1].split('/-- [aspis_r1_cost_probe_program::r1_pool_adapter::owned::authenticate_asq8_accounts',1)[0].strip()
canonical='def fresh'+canonical
assert re.findall(r'\w+|[^\s\w]',body)==re.findall(r'\w+|[^\s\w]',canonical), 'non-layout difference; inspect, never substitute'
changes.append(dict(symbol='column68 whitespace clipping',replacement='token-identical canonical whitespace',token_sha256=hashlib.sha256(' '.join(re.findall(r'\w+|[^\s\w]',body)).encode()).hexdigest()))
body=canonical
header='import AdapterRwModel\nset_option autoImplicit false\nnoncomputable section\nnamespace NND_Registry\nopen Aeneas Aeneas.Std Result ControlFlow Error AdapterRw\n'
footer='''
/-- Fresh frozen control/value definition on the coherent canonical carriers.
This equality alone does not instantiate native decoder slots or RSL effects. -/
theorem adopted (ops : Ops) (v p : solana_pubkey.Pubkey)
 (m : r1_pool_adapter.owned.OwnedAccount)
 (master : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (r e : r1_pool_adapter.owned.OwnedAccount) (slot : U64) :
 fresh ops v p m master r e slot =
 r1_pool_adapter.owned.authenticate_invariant_release_registry ops v p m master r e slot := rfl
#print axioms adopted
end NND_Registry
end
'''
(E/'NND_Registry.lean').write_text(header+body+'\n'+footer)
(E/'NND_REGISTRY_REPLAY.json').write_text(json.dumps(dict(raw=str(raw.relative_to(E)),raw_sha256=hashlib.sha256(raw.read_bytes()).hexdigest(),changes=changes,canonical_types='AdapterRwTypes, structural owner reuse; full carrier-map proof remains separate',std='core.result.Result.map_err interpreted by Aeneas std, no template imported'),indent=1)+'\n')
