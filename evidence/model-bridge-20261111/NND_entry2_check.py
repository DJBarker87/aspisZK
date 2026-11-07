from pathlib import Path
import re
E=Path(__file__).resolve().parent
s=(E/'NND_RegistryV2Head.lean').read_text();s=s[s.index('def decoded'):s.index('\ndef run')]
a=s.index('                                    let a8 ←');b=a+re.search(r'^ {34}\|$',s[a:],re.M).start()
leaf=s[a:b].rstrip();leaf='\n'.join('  '+x[36:] if x.startswith(' '*36) else x for x in leaf.splitlines())
header='''import NND_RegistryV2Head
import NND_RegistryScalarOps
import NND_EntryV2Guard
set_option autoImplicit false
noncomputable section
namespace NND_RegistryEntry2Check
open Aeneas Aeneas.Std Result ControlFlow Error AdapterRw
'''
args='''(ops : Ops) (verifier_program p : solana_pubkey.Pubkey)
 (current_slot : U64) (a6 : Array U8 32#usize)
 (val5 : aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV2) (val7 : solana_pubkey.Pubkey)'''
(E/'NND_RegistryEntry2Check.lean').write_text(header+'def check '+args+' : Result (core.result.Result Unit solana_program_error.ProgramError) := do\n'+leaf+'\n\nend NND_RegistryEntry2Check\nend\n')
args=s[s.index('(ops :'):s.index(' : Result')]
body=s[:a]+'                                    NND_RegistryEntry2Check.check ops verifier_program p current_slot a6 val5 val7\n'+s[b:]
params='ops verifier_program pool_program master_account master registry_account entry_account current_slot registry_program loader val1'
(E/'NND_RegistryV2EntryFactor.lean').write_text(header.replace('namespace NND_RegistryEntry2Check','namespace NND_RegistryV2EntryFactor').replace('import NND_RegistryV2Head','import NND_RegistryEntry2Check')+body.replace('def decoded','def run',1)+'\ntheorem source '+args+' :\n NND_RegistryV2Head.decoded '+params+' = run '+params+' := rfl\n\n#print axioms source\nend NND_RegistryV2EntryFactor\nend\n')
