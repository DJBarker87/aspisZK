from pathlib import Path
calls=[('121','PV_THR2_F6',16,17),('122','PV_THR2_F6',18,19),('123','PV_THR2_F6',20,21),('124','PV_THR2_F6',25,26),('134','PV_THR2_F219',5,6),('410','PV_THR2_F316',7,8)]
header='''import PV_LIB_A_NativeFrontier14
import PV_LIB_A_SpawnEnter12
import PV_THR2_IntrinsicFrameOrdinary
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_PrefixNativeCalls14
open PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap
open PV_LIB_StoreActionTable PV_THR2_SourceStoreLibrary PV_LIB_A_PrefixMachine11
open PV_LIB_A_StructuredFrontier13
abbrev programs := PV_LIB_A_SpawnEnter12.enter270Programs
'''
s=header
for id,mod,node,rest in calls:
 s+=f'''
def src{id} := source {mod}.node{node}
def rest{id} := {mod}.live.body.drop {rest}
theorem shape{id} : PV_LIB_A_StructuredFrontier13.node src{id} :: rest{id} = {mod}.live.body.drop {node} := rfl

theorem child{id} (P : Data → Option PV_STX2_SliceSyntax.Program) : programs P (fn src{id}) = none := by
  rw [programs,PV_LIB_A_SpawnEnter12.enter270Programs,PV_THR2_Source208Table.away]
  · rfl
  · intro eq
    have bad := congrArg PV_THR2_SourceTraitDispatch.source eq
    cases bad

def steps{id} (C : Carrier OWNER Data) := PV_LIB_A_NativeFrontier14.steps C src{id} rest{id}
def after{id} (C : Carrier OWNER Data) (H : Handler) := PV_LIB_A_NativeFrontier14.after C H src{id} rest{id}

theorem run{id} (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (q : State) :
    advance C K (programs P) resources encode H values (steps{id} C q) ⟨q,none⟩ = ⟨after{id} C H q,none⟩ := by
  apply PV_LIB_A_NativeFrontier14.run
  · decide
  · intro s a w; rfl
  · intro t a parents loops vs w es stack
    constructor
    · intro c hc; cases hc
      unfold sourceSelect
      change (match programs P (fn src{id}) with | some _ => none | none => (v2Source (fn src{id})).bind _) = none
      rw [child{id} P]
      rfl
    · intro c hc; cases hc
      cases vs with
      | nil => exact ⟨rfl,rfl,True.intro⟩
      | cons v vs => cases vs <;> exact ⟨rfl,rfl,True.intro⟩
  · intro t a parents loops vs
    apply PV_THR2_IntrinsicFrameOrdinary.run
    intro eq
    have bad := congrArg PV_THR2_OffPath.functionId eq
    cases bad
  · exact child{id} P

#print axioms shape{id}
#print axioms child{id}
#print axioms run{id}
'''
s+='end PV_LIB_A_PrefixNativeCalls14\n'
Path('lean/PV_LIB_A_PrefixNativeCalls14.lean').write_text(s)
