from pathlib import Path
import re,json,hashlib
E=Path(__file__).resolve().parent
s=(E/'NND_Registry.lean').read_text();s=s[s.index('def fresh'):s.index('/-- Fresh frozen')].strip()
header,body=s.split('  := do\n',1)
a=body.index('              let registry_program ← ops.op37 a2')
b=a+re.search(r'^ {12}\| core\.ops\.control_flow\.ControlFlow\.Break residual =>',body[a:],re.M).start()
selected=body[a:b].rstrip()
tail='\n'.join('  '+line[14:] if line.startswith(' '*14) else line for line in selected.splitlines())
args='''(ops : Ops) (verifier_program pool_program : solana_pubkey.Pubkey)
 (master_account : r1_pool_adapter.owned.OwnedAccount)
 (master : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (registry_account entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64)'''
ret='Result (core.result.Result Unit solana_program_error.ProgramError)'
prefix=body[:a]+'              next a2\n'+body[b:]
text='''import NND_Registry
set_option autoImplicit false
noncomputable section
namespace NND_RegistryFactor
open Aeneas Aeneas.Std Result ControlFlow Error AdapterRw
'''
text+='def tail '+args+' (a2 : Array U8 32#usize) : '+ret+' := do\n'+tail+'\n\n'
text+='def head '+args+' (next : Array U8 32#usize → '+ret+') : '+ret+' := do\n'+prefix+'\n\n'
text+='''theorem source (ops : Ops) (v p : solana_pubkey.Pubkey)
 (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (r e : r1_pool_adapter.owned.OwnedAccount) (t : U64) :
 NND_Registry.fresh ops v p m s r e t = head ops v p m s r e t (tail ops v p m s r e t) := rfl
#print axioms source
end NND_RegistryFactor
end
'''
(E/'NND_RegistryFactor.lean').write_text(text)
(E/'NND_REGISTRY_FACTOR.json').write_text(json.dumps(dict(input_sha256=hashlib.sha256(s.encode()).hexdigest(),boundary='after policy Try Continue before registry_program from op37',native_arguments_retained=['ops','verifier_program','pool_program','master_account','master','registry_account','entry_account','current_slot','registry_program bytes op46']),indent=1)+'\n')
