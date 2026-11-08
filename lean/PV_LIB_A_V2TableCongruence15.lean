import PV_LIB_A_OwnerTableCongruence14
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_V2TableCongruence15
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary PV_LIB_StoreActionTable
abbrev Agree := @PV_THR2_TableIntrinsic.Agree

theorem select (P Q : Data → Option PV_STX2_SliceSyntax.Program) (c : Config)
    (same : PV_THR2_TableStepShape.Agree P Q c) :
    PV_LIB_StoreActionTable.select P c = PV_LIB_StoreActionTable.select Q c := by
  unfold PV_LIB_StoreActionTable.select
  cases done : c.frame.completed with
  | some r => rfl
  | none =>
    cases waiting : c.frame.waiting with
    | none => rfl
    | some wait =>
      dsimp only
      cases request : wait.request with
      | child fn a args => simp [request, same wait fn a args done waiting request]
      | copy x y z => simp [request]
      | drop fn x => simp [request]

/-- ORIGINAL v2, including source writers. Full state equality preserves the
native replies, events, worlds and suspended frames on either dispatch arm. -/
theorem step (C : Carrier OWNER Data) (K : Control)
    (P Q : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (s : State)
    (same : Agree P Q s) :
    PV_LIB_StoreActionTable.step C K P resources encode H values s =
      PV_LIB_StoreActionTable.step C K Q resources encode H values s := by
  unfold PV_LIB_StoreActionTable.step
  cases status : s.current.status with
  | running c =>
    simp only
    cases selected : PV_THR2_Catch316Segment.select c with
    | some segment => exact PV_LIB_A_OwnerTableCongruence14.owner C K P Q resources encode H s same
    | none =>
      rw [select P Q c (same c status)]
      cases action : PV_LIB_StoreActionTable.select Q c with
      | none => exact PV_LIB_A_OwnerTableCongruence14.owner C K P Q resources encode H s same
      | some site => rfl
  | returned r store => exact PV_LIB_A_OwnerTableCongruence14.owner C K P Q resources encode H s same
  | fault f store => exact PV_LIB_A_OwnerTableCongruence14.owner C K P Q resources encode H s same
  | undefined site store => exact PV_LIB_A_OwnerTableCongruence14.owner C K P Q resources encode H s same

/-- Finite local lookup certificate; it contains no desired endpoint or return
configuration. Actual callers must establish it from source call descriptors. -/
def Trace (C : Carrier OWNER Data) (K : Control)
    (P Q : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) : Nat → State → Prop
  | 0, _ => True
  | n+1, s => Agree P Q s ∧ Trace C K P Q resources encode H values n
      (PV_LIB_StoreActionTable.step C K P resources encode H values s)

theorem run (C : Carrier OWNER Data) (K : Control)
    (P Q : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (n : Nat) (s : State)
    (trace : Trace C K P Q resources encode H values n s) :
    PV_LIB_StoreActionTable.advance C K P resources encode H values n s =
      PV_LIB_StoreActionTable.advance C K Q resources encode H values n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    change PV_LIB_StoreActionTable.advance C K P resources encode H values n
      (PV_LIB_StoreActionTable.step C K P resources encode H values s) = _
    rw [ih _ trace.2, step C K P Q resources encode H values s trace.1]
    rfl

#print axioms select
#print axioms step
#print axioms Trace
#print axioms run
end PV_LIB_A_V2TableCongruence15
