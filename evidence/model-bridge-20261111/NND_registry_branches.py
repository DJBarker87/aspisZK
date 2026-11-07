from pathlib import Path
import re,json,hashlib
E=Path(__file__).resolve().parent
s=(E/'NND_RegistryFactor.lean').read_text();s=s[s.index('def tail'):s.index('\ndef head')].strip();header,body=s.split(' := do\n',1)
then=body.index('    then\n')+len('    then\n');els=re.search(r'^    else$',body[then:],re.M).start()+then
end=re.search(r'^  \| core\.ops\.control_flow\.ControlFlow\.Break residual =>',body[els:],re.M).start()+els
v2=body[then:els].rstrip();v1=body[els+len('    else\n'):end].rstrip()
def deindent(b):return '\n'.join('  '+x[6:] if x.startswith(' '*6) else x for x in b.splitlines())
args='''(ops : Ops) (verifier_program pool_program : solana_pubkey.Pubkey)
 (master_account : r1_pool_adapter.owned.OwnedAccount)
 (master : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (registry_account entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64)'''
ret='Result (core.result.Result Unit solana_program_error.ProgramError)'
call='ops verifier_program pool_program master_account master registry_account entry_account current_slot registry_program'
out='''import NND_RegistryFactor
set_option autoImplicit false
noncomputable section
namespace NND_RegistryBranches
open Aeneas Aeneas.Std Result ControlFlow Error AdapterRw
'''
for n,b in [('v2',v2),('v1',v1)]:out+='def '+n+' '+args+' (registry_program : solana_pubkey.Pubkey) : '+ret+' := do\n'+deindent(b)+'\n\n'
route=body[:then]+'      v2 '+call+'\n    else\n      v1 '+call+'\n'+body[end:]
out+='def route '+args+' (a2 : Array U8 32#usize) : '+ret+' := do\n'+route+'\n\n'
out+='''theorem source (ops : Ops) (v p : solana_pubkey.Pubkey)
 (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (r e : r1_pool_adapter.owned.OwnedAccount) (t : U64) (a2 : Array U8 32#usize) :
 NND_RegistryFactor.tail ops v p m s r e t a2 = route ops v p m s r e t a2 := rfl
#print axioms source
end NND_RegistryBranches
end
'''
(E/'NND_RegistryBranches.lean').write_text(out)
(E/'NND_REGISTRY_BRANCHES.json').write_text(json.dumps(dict(source_sha256=hashlib.sha256(s.encode()).hexdigest(),boundary='native immutable-deployment flag if, both source branches exact and all catches retained'),indent=1)+'\n')
