from pathlib import Path
import re
E=Path(__file__).resolve().parent
s=(E/'NND_RegistryV1Head.lean').read_text();s=s[s.index('def decoded'):s.index('\ndef run')]
body=s.split(' := do\n',1)[1]
a=body.index('                        let p2 ←')
b=a+re.search(r'^ {22}\|$',body[a:],re.M).start()
leaf=body[a:b].rstrip();leaf='\n'.join('  '+x[24:] if x.startswith(' '*24) else x for x in leaf.splitlines())
header='''import NND_RegistryV1Head
import NND_RegistryScalarOps
import NND_EntryRecordGuards
set_option autoImplicit false
noncomputable section
namespace NND_RegistryEntry1Check
open Aeneas Aeneas.Std Result ControlFlow Error AdapterRw
'''
args='''(ops : Ops) (verifier_program p : solana_pubkey.Pubkey)
 (entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64)
 (val4 : aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV1) (val5 : solana_pubkey.Pubkey)'''
text=header+'def check '+args+' : Result (core.result.Result Unit solana_program_error.ProgramError) := do\n'+leaf+'\n\nend NND_RegistryEntry1Check\nend\n'
(E/'NND_RegistryEntry1Check.lean').write_text(text)
