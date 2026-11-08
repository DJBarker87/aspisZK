import PV_LIB_A_C18_A_RangeQuiet11
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_RangeStartTrace11
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine
open PV_LIB_A_PrefixMachine11
open PV_LIB_A_RangeQuiet11

theorem cons_run (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (H : PV_LIB_StoreActionTable.Handler)
    (n : Nat) (s t : PV_LIB_StoreActionTable.State) (quiet : Quiet P s)
    (one : PV_THR2_IntrinsicState.advance C K P H 1 s = t)
    (tail : Trace C K P H n t) : Trace C K P H (n+1) s := by
  refine ⟨quiet,?_⟩
  change Trace C K P H n (PV_THR2_IntrinsicState.advance C K P H 1 s)
  rw [one]
  exact tail

/-- Opaque165 is neutral in the complete v2 source table as well as the OWNER
layers. This fact inspects its emitted token and saved continuation only. -/
theorem wait165 (P : Data → Option PV_STX2_SliceSyntax.Program)
    (s : Store Data) (a : Nat) (parents : List Frame) (v : Data)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    Quiet (PV_LIB_A_RangePoll11.programs P)
      ⟨⟨.running (PV_THR2_StaticCall.pending s a parents (PV_THR2_F15.live.body.drop 9)
        PV_THR2_Source15RangeChild.fn165 [v] 5),w,es⟩,stack⟩ := by
  constructor
  · intro c hc
    cases hc
    unfold PV_LIB_StoreActionTable.sourceSelect
    change (match PV_LIB_A_RangePoll11.programs P PV_THR2_Source15RangeChild.fn165 with
      | some _ => none
      | none => (PV_LIB_StoreActionTable.v2Source PV_THR2_Source15RangeChild.fn165).bind _) = none
    rw [show PV_LIB_A_RangePoll11.programs P PV_THR2_Source15RangeChild.fn165 = none from
      PV_THR2_Source15RangeChild.child165 P]
    rfl
  · intro c hc
    cases hc
    exact ⟨rfl,rfl,True.intro⟩

/-- The finite certificate for3400/3401, independent of every store value. -/
theorem storage2 (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (H : PV_LIB_StoreActionTable.Handler)
    (s : Store Data) (a : Nat) (parents : List Frame)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    Trace C K P H 2
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F15.live.body.drop 5},parents,s⟩,w,es⟩,stack⟩ := by
  apply cons_run C K P H 1 _ _ (main5 P s a parents [] w es stack)
    (PV_THR2_IntrinsicStorage.run C K P H s a parents (PV_THR2_F15.live.body.drop 6)
      ⟨15,3400,.array [.atom "body",.atom "statements",.number 5]⟩ true 5 w es stack)
  exact ⟨main6 P _ a parents [] w es stack,True.intro⟩

/-- Actual3420 issuance and its full165 poll. The final poll's answer is not
restricted: its source successor is outside this five-step certificate. -/
theorem call2 (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (H : PV_LIB_StoreActionTable.Handler)
    (s : Store Data) (a : Nat) (parents : List Frame) (v : Data)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (cell : s.cells ⟨a,6,[]⟩ = some v) :
    Trace C K (PV_LIB_A_RangePoll11.programs P) H 2
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F15.live.body.drop 8},parents,s⟩,w,es⟩,stack⟩ := by
  apply cons_run C K _ H 1 _ _ (main8 _ s a parents [] w es stack)
    (PV_THR2_Source15Call165.issue C K _ H s a parents v w es stack cell)
  exact ⟨wait165 P _ a parents v w es stack,True.intro⟩

/-- Concrete five-step prefix certificate, not a new consumer/row assumption.
Compose the provider's named storage/aggregate runs without reducing stores. -/
theorem prefix5 (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (H : PV_LIB_StoreActionTable.Handler)
    (s : Store Data) (a : Nat) (parents : List Frame) (b : Bool)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    Trace (PV_THR2_OwnInitExactReturnedCases.carrier C b) K
      (PV_LIB_A_RangePoll11.programs P) H 5
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F15.live.body.drop 5},parents,s⟩,w,es⟩,stack⟩ := by
  let B := PV_THR2_OwnInitExactReturnedCases.carrier C b
  let T := PV_LIB_A_RangePoll11.programs P
  apply append B K T H 2 3 _ (storage2 B K T H s a parents w es stack)
  rw [PV_THR2_Source15RangeStorage.run]
  apply cons_run B K T H 2 _ _ (main7 T _ a parents [] w es stack)
    (PV_THR2_Source15RangeAggregate.run C K T H _ a parents b w es stack)
  apply call2 B K P H _ a parents PV_THR2_Source15RangeAggregate.value w es stack
  exact write_same _ _ _

#print axioms cons_run
#print axioms wait165
#print axioms storage2
#print axioms call2
#print axioms prefix5
end PV_LIB_A_RangeStartTrace11
