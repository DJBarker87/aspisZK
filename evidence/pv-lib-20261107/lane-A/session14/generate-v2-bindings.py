from pathlib import Path
import re
s='''import PV_LIB_A_V2PrefixTables14
import PV_LIB_A_V2NativeFrontier14
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_V2PrefixBindings14
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary PV_LIB_StoreActionTable
open PV_LIB_A_PrefixMachine11 PV_LIB_A_StructuredFrontier13 PV_LIB_A_V2PrefixTables14
'''
for mod,kind in [('PV_LIB_A_PrefixNativeCalls14','native'),('PV_LIB_A_PrefixStructuredCalls14','body')]:
 raw=Path('lean',mod+'.lean').read_text()
 for n,theorem in re.findall(r'theorem run(\d+) (.*?)(?=\n#print axioms)',raw,re.S):
  s+=f'''\nabbrev src{n} := {mod}.src{n}
abbrev rest{n} := {mod}.rest{n}
abbrev steps{n} := {mod}.steps{n}
abbrev after{n} := {mod}.after{n}
'''
  t='theorem run'+n+' '+theorem
  t=t.replace('(P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources)', '(P : Data → Option PV_STX2_SliceSyntax.Program) (tables : Tables P) (resources : Resources)')
  t=t.replace('advance C K (programs P)','PV_LIB_StoreActionTable.advance C K P').replace('(steps'+n+' C q) ⟨q,none⟩ = ⟨after'+n+' C H q,none⟩','(steps'+n+' C q) q = after'+n+' C H q').replace('(steps'+n+' C q) ⟨q,none⟩ = ⟨after'+n+' C q,none⟩','(steps'+n+' C q) q = after'+n+' C q')
  t=t.replace('match programs P (fn','match P (fn').replace('PV_LIB_A_NativeFrontier14.run','PV_LIB_A_V2NativeFrontier14.run').replace('PV_LIB_A_StructuredFrontier13.run','PV_LIB_A_V2Frontiers14.structured')
  t=t.replace('child'+n+' P','tables.native'+n).replace('lookup'+n+' P','tables.body'+n)
  s+=t+'\n#print axioms run'+n+'\n'
s+='end PV_LIB_A_V2PrefixBindings14\n';Path('lean/PV_LIB_A_V2PrefixBindings14.lean').write_text(s)
