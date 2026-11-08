import PV_LIB_A_StructuredFrontier13
import PV_LIB_A_SpawnEnter12
import PV_THR2_IntrinsicFrameOrdinary
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_PrefixStructuredCalls14
open PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap
open PV_LIB_StoreActionTable PV_THR2_SourceStoreLibrary PV_LIB_A_PrefixMachine11
open PV_LIB_A_StructuredFrontier13
abbrev programs := PV_LIB_A_SpawnEnter12.enter270Programs

def src125 := source PV_THR2_F6.node45
def rest125 := PV_THR2_F6.live.body.drop 46
theorem shape125 : PV_LIB_A_StructuredFrontier13.node src125 :: rest125 = PV_THR2_F6.live.body.drop 45 := rfl

theorem lookup125 (P : Data → Option PV_STX2_SliceSyntax.Program) : programs P (fn src125) = some PV_THR2_F125.live := by
  rw [programs,PV_LIB_A_SpawnEnter12.enter270Programs,PV_THR2_Source208Table.away]
  · rfl
  · intro eq
    have bad := congrArg PV_THR2_SourceTraitDispatch.source eq
    cases bad

def steps125 (C : Carrier OWNER Data) := PV_LIB_A_StructuredFrontier13.steps C src125 rest125
def after125 (C : Carrier OWNER Data) := PV_LIB_A_StructuredFrontier13.after C src125 rest125 PV_THR2_F125.live
theorem run125 (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (q : State) :
    advance C K (programs P) resources encode H values (steps125 C q) ⟨q,none⟩ = ⟨after125 C q,none⟩ := by
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
    cases bad
  · intro s a w; rfl
  · exact lookup125 P

#print axioms shape125
#print axioms lookup125
#print axioms run125

def src219 := source PV_THR2_F125.node3
def rest219 := PV_THR2_F125.live.body.drop 4
theorem shape219 : PV_LIB_A_StructuredFrontier13.node src219 :: rest219 = PV_THR2_F125.live.body.drop 3 := rfl

theorem lookup219 (P : Data → Option PV_STX2_SliceSyntax.Program) : programs P (fn src219) = some PV_THR2_F219.live := by
  rw [programs,PV_LIB_A_SpawnEnter12.enter270Programs,PV_THR2_Source208Table.away]
  · rfl
  · intro eq
    have bad := congrArg PV_THR2_SourceTraitDispatch.source eq
    cases bad

def steps219 (C : Carrier OWNER Data) := PV_LIB_A_StructuredFrontier13.steps C src219 rest219
def after219 (C : Carrier OWNER Data) := PV_LIB_A_StructuredFrontier13.after C src219 rest219 PV_THR2_F219.live
theorem run219 (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (q : State) :
    advance C K (programs P) resources encode H values (steps219 C q) ⟨q,none⟩ = ⟨after219 C q,none⟩ := by
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
    cases bad
  · intro s a w; rfl
  · exact lookup219 P

#print axioms shape219
#print axioms lookup219
#print axioms run219

def src220 := source PV_THR2_F316.node16
def rest220 := PV_THR2_F316.live.body.drop 17
theorem shape220 : PV_LIB_A_StructuredFrontier13.node src220 :: rest220 = PV_THR2_F316.live.body.drop 16 := rfl

theorem lookup220 (P : Data → Option PV_STX2_SliceSyntax.Program) : programs P (fn src220) = some PV_THR2_F220.live := by
  rw [programs,PV_LIB_A_SpawnEnter12.enter270Programs,PV_THR2_Source208Table.away]
  · rfl
  · intro eq
    have bad := congrArg PV_THR2_SourceTraitDispatch.source eq
    cases bad

def steps220 (C : Carrier OWNER Data) := PV_LIB_A_StructuredFrontier13.steps C src220 rest220
def after220 (C : Carrier OWNER Data) := PV_LIB_A_StructuredFrontier13.after C src220 rest220 PV_THR2_F220.live
theorem run220 (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (q : State) :
    advance C K (programs P) resources encode H values (steps220 C q) ⟨q,none⟩ = ⟨after220 C q,none⟩ := by
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
    cases bad
  · intro s a w; rfl
  · exact lookup220 P

#print axioms shape220
#print axioms lookup220
#print axioms run220

def src208 := source PV_THR2_F220.node5
def rest208 := PV_THR2_F220.live.body.drop 6
theorem shape208 : PV_LIB_A_StructuredFrontier13.node src208 :: rest208 = PV_THR2_F220.live.body.drop 5 := rfl

theorem lookup208 (P : Data → Option PV_STX2_SliceSyntax.Program) : programs P (fn src208) = some PV_THR2_F208.live := by
  rw [programs,PV_LIB_A_SpawnEnter12.enter270Programs,PV_THR2_Source208Table.away]
  · rfl
  · intro eq
    have bad := congrArg PV_THR2_SourceTraitDispatch.source eq
    cases bad

def steps208 (C : Carrier OWNER Data) := PV_LIB_A_StructuredFrontier13.steps C src208 rest208
def after208 (C : Carrier OWNER Data) := PV_LIB_A_StructuredFrontier13.after C src208 rest208 PV_THR2_F208.live
theorem run208 (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (q : State) :
    advance C K (programs P) resources encode H values (steps208 C q) ⟨q,none⟩ = ⟨after208 C q,none⟩ := by
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
    cases bad
  · intro s a w; rfl
  · exact lookup208 P

#print axioms shape208
#print axioms lookup208
#print axioms run208

def src15 := source PV_THR2_F208.node11
def rest15 := PV_THR2_F208.live.body.drop 12
theorem shape15 : PV_LIB_A_StructuredFrontier13.node src15 :: rest15 = PV_THR2_F208.live.body.drop 11 := rfl

theorem lookup15 (P : Data → Option PV_STX2_SliceSyntax.Program) : programs P (fn src15) = some PV_THR2_F15.live := by
  exact PV_THR2_Source208Table.at208 _

def steps15 (C : Carrier OWNER Data) := PV_LIB_A_StructuredFrontier13.steps C src15 rest15
def after15 (C : Carrier OWNER Data) := PV_LIB_A_StructuredFrontier13.after C src15 rest15 PV_THR2_F15.live
theorem run15 (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (q : State) :
    advance C K (programs P) resources encode H values (steps15 C q) ⟨q,none⟩ = ⟨after15 C q,none⟩ := by
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
    cases bad
  · intro s a w; rfl
  · exact lookup15 P

#print axioms shape15
#print axioms lookup15
#print axioms run15
end PV_LIB_A_PrefixStructuredCalls14
