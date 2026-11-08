import PV_LIB_A_NativeFrontier14
import PV_LIB_A_SpawnEnter12
import PV_THR2_IntrinsicFrameOrdinary
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_PrefixNativeCalls14
open PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap
open PV_LIB_StoreActionTable PV_THR2_SourceStoreLibrary PV_LIB_A_PrefixMachine11
open PV_LIB_A_StructuredFrontier13
abbrev programs := PV_LIB_A_SpawnEnter12.enter270Programs

def src121 := source PV_THR2_F6.node16
def rest121 := PV_THR2_F6.live.body.drop 17
theorem shape121 : PV_LIB_A_StructuredFrontier13.node src121 :: rest121 = PV_THR2_F6.live.body.drop 16 := rfl

theorem child121 (P : Data → Option PV_STX2_SliceSyntax.Program) : programs P (fn src121) = none := by
  rw [programs,PV_LIB_A_SpawnEnter12.enter270Programs,PV_THR2_Source208Table.away]
  · rfl
  · intro eq
    have bad := congrArg PV_THR2_SourceTraitDispatch.source eq
    cases bad

def steps121 (C : Carrier OWNER Data) := PV_LIB_A_NativeFrontier14.steps C src121 rest121
def after121 (C : Carrier OWNER Data) (H : Handler) := PV_LIB_A_NativeFrontier14.after C H src121 rest121

theorem run121 (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (q : State) :
    advance C K (programs P) resources encode H values (steps121 C q) ⟨q,none⟩ = ⟨after121 C H q,none⟩ := by
  apply PV_LIB_A_NativeFrontier14.run
  · decide
  · intro s a w; rfl
  · intro t a parents loops vs w es stack
    constructor
    · intro c hc; cases hc
      unfold sourceSelect
      change (match programs P (fn src121) with | some _ => none | none => (v2Source (fn src121)).bind _) = none
      rw [child121 P]
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
  · exact child121 P

#print axioms shape121
#print axioms child121
#print axioms run121

def src122 := source PV_THR2_F6.node18
def rest122 := PV_THR2_F6.live.body.drop 19
theorem shape122 : PV_LIB_A_StructuredFrontier13.node src122 :: rest122 = PV_THR2_F6.live.body.drop 18 := rfl

theorem child122 (P : Data → Option PV_STX2_SliceSyntax.Program) : programs P (fn src122) = none := by
  rw [programs,PV_LIB_A_SpawnEnter12.enter270Programs,PV_THR2_Source208Table.away]
  · rfl
  · intro eq
    have bad := congrArg PV_THR2_SourceTraitDispatch.source eq
    cases bad

def steps122 (C : Carrier OWNER Data) := PV_LIB_A_NativeFrontier14.steps C src122 rest122
def after122 (C : Carrier OWNER Data) (H : Handler) := PV_LIB_A_NativeFrontier14.after C H src122 rest122

theorem run122 (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (q : State) :
    advance C K (programs P) resources encode H values (steps122 C q) ⟨q,none⟩ = ⟨after122 C H q,none⟩ := by
  apply PV_LIB_A_NativeFrontier14.run
  · decide
  · intro s a w; rfl
  · intro t a parents loops vs w es stack
    constructor
    · intro c hc; cases hc
      unfold sourceSelect
      change (match programs P (fn src122) with | some _ => none | none => (v2Source (fn src122)).bind _) = none
      rw [child122 P]
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
  · exact child122 P

#print axioms shape122
#print axioms child122
#print axioms run122

def src123 := source PV_THR2_F6.node20
def rest123 := PV_THR2_F6.live.body.drop 21
theorem shape123 : PV_LIB_A_StructuredFrontier13.node src123 :: rest123 = PV_THR2_F6.live.body.drop 20 := rfl

theorem child123 (P : Data → Option PV_STX2_SliceSyntax.Program) : programs P (fn src123) = none := by
  rw [programs,PV_LIB_A_SpawnEnter12.enter270Programs,PV_THR2_Source208Table.away]
  · rfl
  · intro eq
    have bad := congrArg PV_THR2_SourceTraitDispatch.source eq
    cases bad

def steps123 (C : Carrier OWNER Data) := PV_LIB_A_NativeFrontier14.steps C src123 rest123
def after123 (C : Carrier OWNER Data) (H : Handler) := PV_LIB_A_NativeFrontier14.after C H src123 rest123

theorem run123 (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (q : State) :
    advance C K (programs P) resources encode H values (steps123 C q) ⟨q,none⟩ = ⟨after123 C H q,none⟩ := by
  apply PV_LIB_A_NativeFrontier14.run
  · decide
  · intro s a w; rfl
  · intro t a parents loops vs w es stack
    constructor
    · intro c hc; cases hc
      unfold sourceSelect
      change (match programs P (fn src123) with | some _ => none | none => (v2Source (fn src123)).bind _) = none
      rw [child123 P]
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
  · exact child123 P

#print axioms shape123
#print axioms child123
#print axioms run123

def src124 := source PV_THR2_F6.node25
def rest124 := PV_THR2_F6.live.body.drop 26
theorem shape124 : PV_LIB_A_StructuredFrontier13.node src124 :: rest124 = PV_THR2_F6.live.body.drop 25 := rfl

theorem child124 (P : Data → Option PV_STX2_SliceSyntax.Program) : programs P (fn src124) = none := by
  rw [programs,PV_LIB_A_SpawnEnter12.enter270Programs,PV_THR2_Source208Table.away]
  · rfl
  · intro eq
    have bad := congrArg PV_THR2_SourceTraitDispatch.source eq
    cases bad

def steps124 (C : Carrier OWNER Data) := PV_LIB_A_NativeFrontier14.steps C src124 rest124
def after124 (C : Carrier OWNER Data) (H : Handler) := PV_LIB_A_NativeFrontier14.after C H src124 rest124

theorem run124 (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (q : State) :
    advance C K (programs P) resources encode H values (steps124 C q) ⟨q,none⟩ = ⟨after124 C H q,none⟩ := by
  apply PV_LIB_A_NativeFrontier14.run
  · decide
  · intro s a w; rfl
  · intro t a parents loops vs w es stack
    constructor
    · intro c hc; cases hc
      unfold sourceSelect
      change (match programs P (fn src124) with | some _ => none | none => (v2Source (fn src124)).bind _) = none
      rw [child124 P]
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
  · exact child124 P

#print axioms shape124
#print axioms child124
#print axioms run124

def src134 := source PV_THR2_F219.node5
def rest134 := PV_THR2_F219.live.body.drop 6
theorem shape134 : PV_LIB_A_StructuredFrontier13.node src134 :: rest134 = PV_THR2_F219.live.body.drop 5 := rfl

theorem child134 (P : Data → Option PV_STX2_SliceSyntax.Program) : programs P (fn src134) = none := by
  rw [programs,PV_LIB_A_SpawnEnter12.enter270Programs,PV_THR2_Source208Table.away]
  · rfl
  · intro eq
    have bad := congrArg PV_THR2_SourceTraitDispatch.source eq
    cases bad

def steps134 (C : Carrier OWNER Data) := PV_LIB_A_NativeFrontier14.steps C src134 rest134
def after134 (C : Carrier OWNER Data) (H : Handler) := PV_LIB_A_NativeFrontier14.after C H src134 rest134

theorem run134 (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (q : State) :
    advance C K (programs P) resources encode H values (steps134 C q) ⟨q,none⟩ = ⟨after134 C H q,none⟩ := by
  apply PV_LIB_A_NativeFrontier14.run
  · decide
  · intro s a w; rfl
  · intro t a parents loops vs w es stack
    constructor
    · intro c hc; cases hc
      unfold sourceSelect
      change (match programs P (fn src134) with | some _ => none | none => (v2Source (fn src134)).bind _) = none
      rw [child134 P]
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
  · exact child134 P

#print axioms shape134
#print axioms child134
#print axioms run134

def src410 := source PV_THR2_F316.node7
def rest410 := PV_THR2_F316.live.body.drop 8
theorem shape410 : PV_LIB_A_StructuredFrontier13.node src410 :: rest410 = PV_THR2_F316.live.body.drop 7 := rfl

theorem child410 (P : Data → Option PV_STX2_SliceSyntax.Program) : programs P (fn src410) = none := by
  rw [programs,PV_LIB_A_SpawnEnter12.enter270Programs,PV_THR2_Source208Table.away]
  · rfl
  · intro eq
    have bad := congrArg PV_THR2_SourceTraitDispatch.source eq
    cases bad

def steps410 (C : Carrier OWNER Data) := PV_LIB_A_NativeFrontier14.steps C src410 rest410
def after410 (C : Carrier OWNER Data) (H : Handler) := PV_LIB_A_NativeFrontier14.after C H src410 rest410

theorem run410 (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (q : State) :
    advance C K (programs P) resources encode H values (steps410 C q) ⟨q,none⟩ = ⟨after410 C H q,none⟩ := by
  apply PV_LIB_A_NativeFrontier14.run
  · decide
  · intro s a w; rfl
  · intro t a parents loops vs w es stack
    constructor
    · intro c hc; cases hc
      unfold sourceSelect
      change (match programs P (fn src410) with | some _ => none | none => (v2Source (fn src410)).bind _) = none
      rw [child410 P]
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
  · exact child410 P

#print axioms shape410
#print axioms child410
#print axioms run410
end PV_LIB_A_PrefixNativeCalls14
