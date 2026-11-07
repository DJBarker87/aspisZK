from pathlib import Path
import re
E=Path(__file__).resolve().parent
s=(E/'NND_RegistryBranches.lean').read_text();s=s[s.index('def v1'):s.index('\ndef route')].strip();_,body=s.split(' := do\n',1)
a=body.index('      let p ←')
b=a+re.search(r'^ {4}\| core\.ops\.control_flow\.ControlFlow\.Break residual =>',body[a:],re.M).start()
selected=body[a:b].rstrip()
decoded='\n'.join('  '+x[6:] if x.startswith(' '*6) else x for x in selected.splitlines())
args='''(ops : Ops) (verifier_program pool_program : solana_pubkey.Pubkey)
 (master_account : r1_pool_adapter.owned.OwnedAccount)
 (master : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (registry_account entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64)
 (registry_program : solana_pubkey.Pubkey)'''
ret='Result (core.result.Result Unit solana_program_error.ProgramError)'
text='''import NND_RegistryBranches
import NND_FormatControl
set_option autoImplicit false
noncomputable section
namespace NND_RegistryV1Head
open Aeneas Aeneas.Std Result ControlFlow Error AdapterRw
'''
text+='def decoded '+args+' (val1 : aspis_statement.pool_v1.verifier_registry.VerifierRegistryV1) : '+ret+' := do\n'+decoded+'\n\n'
runbody=body[:a]+'      decoded ops verifier_program pool_program master_account master registry_account entry_account current_slot registry_program val1\n'+body[b:]
text+='def run '+args+' : '+ret+' := do\n'+runbody+'\n'
text+='''
theorem source (ops : Ops) (v p : solana_pubkey.Pubkey)
 (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (r e : r1_pool_adapter.owned.OwnedAccount) (t : U64) (rp : solana_pubkey.Pubkey) :
 NND_RegistryBranches.v1 ops v p m s r e t rp = run ops v p m s r e t rp := rfl

#print axioms source
end NND_RegistryV1Head
end
'''
(E/'NND_RegistryV1Head.lean').write_text(text.replace('core.result.Result.map_err','AdapterRw.core.result.Result.map_err'))
