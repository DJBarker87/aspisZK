from pathlib import Path
import re
E=Path(__file__).resolve().parent
s=(E/'NND_RegistryV1Head.lean').read_text();s=s[s.index('def decoded'):s.index('\ndef run')]
a=s.index('                        let p2 ←');b=a+re.search(r'^ {22}\|$',s[a:],re.M).start()
body=s[:a]+'                        NND_RegistryEntry1Check.check ops verifier_program p entry_account current_slot val4 val5\n'+s[b:]
body=body.replace('def decoded','def run',1)
args=s[s.index('(ops :'):s.index(' : Result')]
params='ops verifier_program pool_program master_account master registry_account entry_account current_slot registry_program val1'
out='''import NND_RegistryEntry1Check
set_option autoImplicit false
noncomputable section
namespace NND_RegistryV1EntryFactor
open Aeneas Aeneas.Std Result ControlFlow Error AdapterRw
'''+body+'\ntheorem source '+args+' :\n NND_RegistryV1Head.decoded '+params+' = run '+params+' := rfl\n\n#print axioms source\nend NND_RegistryV1EntryFactor\nend\n'
(E/'NND_RegistryV1EntryFactor.lean').write_text(out)
