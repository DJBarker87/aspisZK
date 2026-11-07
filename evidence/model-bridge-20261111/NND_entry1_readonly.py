from pathlib import Path
import re
E=Path(__file__).resolve().parent
s=(E/'NND_RegistryV1DecodeFactor.lean').read_text();s=s[s.index('def run'):s.index('\ntheorem source')]
a=s.index('                let r8 ←');b=a+re.search(r'^ {12}else$',s[a:],re.M).start()
leaf=s[a:b].rstrip();leaf='\n'.join('  '+x[16:] if x.startswith(' '*16) else x for x in leaf.splitlines())
args='''(ops : Ops) (verifier_program p registry_program : solana_pubkey.Pubkey)
 (entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64)'''
header='''import NND_RegistryV1DecodeFactor
import NND_Entry1DecodedValue
set_option autoImplicit false
noncomputable section
namespace NND_Entry1Readonly
open Aeneas Aeneas.Std Result ControlFlow Error AdapterRw NND_Carrier NND_Returned
'''
(E/'NND_Entry1Readonly.lean').write_text(header+'def run '+args+' : Result (core.result.Result Unit solana_program_error.ProgramError) := do\n'+leaf+'\n\nend NND_Entry1Readonly\nend\n')
args=s[s.index('(ops :'):s.index(' : Result')]
body=s[:a]+'                NND_Entry1Readonly.run ops verifier_program p registry_program entry_account current_slot\n'+s[b:]
params='ops verifier_program pool_program master_account master registry_account entry_account current_slot registry_program val1'
(E/'NND_RegistryV1ReadonlyFactor.lean').write_text(header.replace('import NND_RegistryV1DecodeFactor','import NND_Entry1Readonly').replace('namespace NND_Entry1Readonly','namespace NND_RegistryV1ReadonlyFactor')+body+'\ntheorem source '+args+' :\n NND_RegistryV1DecodeFactor.run '+params+' = run '+params+' := rfl\n\n#print axioms source\nend NND_RegistryV1ReadonlyFactor\nend\n')
