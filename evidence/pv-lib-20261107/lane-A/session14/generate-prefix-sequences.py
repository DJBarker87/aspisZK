from pathlib import Path
s='''import PV_LIB_A_SequenceFrontier13
import PV_LIB_A_PrefixNativeCalls14
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_F6SourceSequences14
open PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap
open PV_LIB_StoreActionTable PV_THR2_SourceStoreLibrary PV_LIB_A_PrefixMachine11
open PV_LIB_A_SourceSequence13 PV_LIB_A_SequenceFrontier13
'''
for name,start,end in [('A',0,16),('B',17,18),('C',19,20),('D',21,25),('E',26,45)]:
 seq='.done'
 for i in reversed(range(start,end)):seq=f'prepend PV_THR2_F6.node{i} ({seq})'
 s+=f'''
def seq{name} : Seq := {seq}
theorem shape{name} : nodes seq{name} ++ PV_THR2_F6.live.body.drop {end} = PV_THR2_F6.live.body.drop {start} := rfl
theorem off{name} : sites seq{name} := by
  change {' ∧ '.join(['(6 : Nat) ≠ 361']*(end-start)+['True'])}
  decide

def steps{name} (C : Carrier OWNER Data) := PV_LIB_A_SequenceFrontier13.steps C seq{name} (PV_THR2_F6.live.body.drop {end})
def after{name} (C : Carrier OWNER Data) := PV_LIB_A_SequenceFrontier13.after C seq{name} (PV_THR2_F6.live.body.drop {end})
theorem run{name} (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (q : State) :
    advance C K P resources encode H values (steps{name} C q) ⟨q,none⟩ = ⟨after{name} C q,none⟩ :=
  PV_LIB_A_SequenceFrontier13.run C K P resources encode H values seq{name} _ off{name} q

#print axioms shape{name}
#print axioms off{name}
#print axioms run{name}
'''
s+='end PV_LIB_A_F6SourceSequences14\n';Path('lean/PV_LIB_A_F6SourceSequences14.lean').write_text(s)
