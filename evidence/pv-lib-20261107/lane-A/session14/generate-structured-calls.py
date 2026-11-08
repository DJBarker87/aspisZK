from pathlib import Path
calls=[('125','PV_THR2_F6',45,46,'PV_THR2_F125.live'),('219','PV_THR2_F125',3,4,'PV_THR2_F219.live'),('220','PV_THR2_F316',16,17,'PV_THR2_F220.live'),('208','PV_THR2_F220',5,6,'PV_THR2_F208.live'),('15','PV_THR2_F208',11,12,'PV_THR2_F15.live')]
s='''import PV_LIB_A_StructuredFrontier13
import PV_LIB_A_SpawnEnter12
import PV_THR2_IntrinsicFrameOrdinary
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_PrefixStructuredCalls14
open PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap
open PV_LIB_StoreActionTable PV_THR2_SourceStoreLibrary PV_LIB_A_PrefixMachine11
open PV_LIB_A_StructuredFrontier13
abbrev programs := PV_LIB_A_SpawnEnter12.enter270Programs
'''
for id,mod,n,rest,body in calls:
 s+=f'''
def src{id} := source {mod}.node{n}
def rest{id} := {mod}.live.body.drop {rest}
theorem shape{id} : PV_LIB_A_StructuredFrontier13.node src{id} :: rest{id} = {mod}.live.body.drop {n} := rfl

theorem lookup{id} (P : Data → Option PV_STX2_SliceSyntax.Program) : programs P (fn src{id}) = some {body} := by
'''
 if id=='15':s+='  exact PV_THR2_Source208Table.at208 _\n'
 else:
  s+='''  rw [programs,PV_LIB_A_SpawnEnter12.enter270Programs,PV_THR2_Source208Table.away]
  · rfl
  · intro eq
    have bad := congrArg PV_THR2_SourceTraitDispatch.source eq
    cases bad
'''
 s+=f'''
def steps{id} (C : Carrier OWNER Data) := PV_LIB_A_StructuredFrontier13.steps C src{id} rest{id}
def after{id} (C : Carrier OWNER Data) := PV_LIB_A_StructuredFrontier13.after C src{id} rest{id} {body}
theorem run{id} (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (q : State) :
    advance C K (programs P) resources encode H values (steps{id} C q) ⟨q,none⟩ = ⟨after{id} C q,none⟩ := by
  apply PV_LIB_A_StructuredFrontier13.run
  · decide
  · intro t a parents loops vs
    cases vs with
    | nil => exact ⟨rfl,rfl⟩
    | cons v vs => cases vs <;> exact ⟨rfl,rfl⟩
  · intro t a parents loops vs
    apply PV_THR2_IntrinsicFrameOrdinary.run
    intro eq
    have bad := congrArg PV_THR2_OffPath.functionId eq
'''
 if id in ['220','208','15']:
  # Trait fn has no regular id; intrinsic318 has some318.
  s+='    cases bad\n'
 else:s+='    cases bad\n'
 s+=f'''  · intro s a w; rfl
  · exact lookup{id} P

#print axioms shape{id}
#print axioms lookup{id}
#print axioms run{id}
'''
s+='end PV_LIB_A_PrefixStructuredCalls14\n';Path('lean/PV_LIB_A_PrefixStructuredCalls14.lean').write_text(s)
