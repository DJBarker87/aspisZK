import PV_LIB_A_WeakGuardCorrected10
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_WeakGuardPrefix10
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
open PV_LIB_StoreActionTable PV_LIB_A_WeakGuardCorrected10

/-- Repeated corrected transitions, with every retained phase part of state. -/
def advance (next : SourceState → SourceState) : Nat → SourceState → SourceState
  | 0,s => s
  | n+1,s => next (advance next n s)

/-- Six actual source instructions on the OWNER-aware machine, before the683
poll. Neither the handler nor resources have been called in this prefix. -/
theorem run (C : Carrier OWNER Data) (K : Control) (b : Bool)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (types : List Data) (s : Store Data) (a : Nat) (parents : List Frame)
    (p : Address) (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (n : Nat) (bound : n ≤ 6) :
    advance (PV_LIB_A_WeakOwnerFree10.step
      (PV_THR2_OwnInitExactReturnedCases.carrier C b) K P resources encode H values) n
      ⟨⟨⟨.running (configuration types s a parents p 0),w,es⟩,stack⟩,none⟩ =
      ⟨⟨⟨.running (configuration types s a parents p n),w,es⟩,stack⟩,none⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [advance,ih (by omega)]
    exact corrected_step C K b P resources encode H values types s a parents p w es stack n (by omega)

/-- Reads of older allocation roots survive the REAL issued prefix, including
its call-argument writes. Field traversal remains the same carrier operation. -/
theorem source_read (C : Carrier OWNER Data) (b : Bool) (s : Store Data)
    (a : Nat) (p q : Address)
    (older : q.activation ≠ a) (fresh : q.activation ≠ s.nextActivation) :
    readAddress (PV_LIB_A_DestructorValues10.carrier C b)
      (PV_LIB_A_WeakGuardSource10.prepared s a p) q =
    readAddress (PV_LIB_A_DestructorValues10.carrier C b) s q := by
  unfold readAddress
  rw [PV_LIB_A_WeakGuardSource10.older_cell s a p {q with fields := []} older fresh]

#print axioms advance
#print axioms run
#print axioms source_read
end PV_LIB_A_WeakGuardPrefix10
