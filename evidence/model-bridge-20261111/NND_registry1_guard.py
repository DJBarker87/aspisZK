from pathlib import Path
import re
E=Path(__file__).resolve().parent
s=(E/'NND_RegistryV1ReadonlyFactor.lean').read_text();s=s[s.index('def run'):s.index('\ntheorem source')]
a=s.index('    let p1 ←');b=a+re.search(r'^ {2}\|',s[a:],re.M).start()
leaf=s[a:b].rstrip();leaf='\n'.join('  '+x[4:] if x.startswith(' '*4) else x for x in leaf.splitlines())
args='''(ops : Ops) (verifier_program p registry_program : solana_pubkey.Pubkey)
 (master : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (registry_account entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64)
 (val1 : aspis_statement.pool_v1.verifier_registry.VerifierRegistryV1) (val2 : solana_pubkey.Pubkey)'''
header='''import NND_RegistryV1ReadonlyFactor
import NND_RegistryFlagValues
set_option autoImplicit false
noncomputable section
namespace NND_Registry1Guard
open Aeneas Aeneas.Std Result ControlFlow Error AdapterRw NND_Carrier NND_Returned
'''
(E/'NND_Registry1Guard.lean').write_text(header+'def run '+args+' : Result (core.result.Result Unit solana_program_error.ProgramError) := do\n'+leaf+'\n\nend NND_Registry1Guard\nend\n')
args=s[s.index('(ops :'):s.index(' : Result')]
body=s[:a]+'    NND_Registry1Guard.run ops verifier_program p registry_program master registry_account entry_account current_slot val1 val2\n'+s[b:]
params='ops verifier_program pool_program master_account master registry_account entry_account current_slot registry_program val1'
(E/'NND_RegistryV1GuardFactor.lean').write_text(header.replace('import NND_RegistryV1ReadonlyFactor','import NND_Registry1Guard').replace('namespace NND_Registry1Guard','namespace NND_RegistryV1GuardFactor')+body+'\ntheorem source '+args+' :\n NND_RegistryV1ReadonlyFactor.run '+params+' = run '+params+' := rfl\n\n#print axioms source\nend NND_RegistryV1GuardFactor\nend\n')
