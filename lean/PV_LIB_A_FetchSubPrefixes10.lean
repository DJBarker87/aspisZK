import PV_LIB_A_FetchSubMachine10
import PV_LIB_A_WeakGuardBuildPrefix10
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_FetchSubPrefixes10
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
open PV_LIB_StoreActionTable

def advance {S : Type} (next : S → S) : Nat → S → S
  | 0,s => s
  | n+1,s => next (advance next n s)

/-- All ordinary source instructions retain the identical underlying OWNER
step; the snapshot layer cannot alter them or add a hidden source operation. -/
theorem nonwaiting (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (c : Config) (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (waiting : c.frame.waiting = none) :
    PV_LIB_A_FetchSubMachine10.step C K P resources encode H values
      (PV_LIB_A_FetchSubMachine10.wrap ⟨⟨⟨.running c,w,es⟩,stack⟩,none⟩) =
      PV_LIB_A_FetchSubMachine10.wrap (PV_LIB_A_WeakOwnerFree10.step C K P resources encode H values
        ⟨⟨⟨.running c,w,es⟩,stack⟩,none⟩) := by
  apply PV_LIB_A_FetchSubMachine10.agreement _ _ _ _ _ _ _ _ rfl
  intro d hd
  cases hd
  simp [PV_LIB_A_FetchSubReply10.selected,sourceSelect,waiting]
  cases c.frame.completed <;> simp

/-- Revalidate the exact661 prefix on the LATEST snapshot-aware machine. -/
theorem guard_run (C : Carrier OWNER Data) (K : Control) (b : Bool)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (types : List Data) (s : Store Data) (a : Nat) (parents : List Frame)
    (p : Address) (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (n : Nat) (bound : n ≤ 6) :
    advance (PV_LIB_A_FetchSubMachine10.step (PV_THR2_OwnInitExactReturnedCases.carrier C b)
      K P resources encode H values) n (PV_LIB_A_FetchSubMachine10.wrap
        ⟨⟨⟨.running (PV_LIB_A_WeakGuardCorrected10.configuration types s a parents p 0),w,es⟩,stack⟩,none⟩) =
      PV_LIB_A_FetchSubMachine10.wrap
        ⟨⟨⟨.running (PV_LIB_A_WeakGuardCorrected10.configuration types s a parents p n),w,es⟩,stack⟩,none⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [advance,ih (by omega),nonwaiting]
    · rw [PV_LIB_A_WeakGuardCorrected10.corrected_step C K b P resources encode H values
        types s a parents p w es stack n (by omega)]
    · simp [PV_LIB_A_WeakGuardCorrected10.configuration,show n ≠ 6 by omega]

/-- Revalidate actual584's guard construction on the SAME latest machine. -/
theorem build_run (C : Carrier OWNER Data) (K : Control) (b : Bool)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (types : List Data) (s : Store Data) (a : Nat) (parents : List Frame)
    (root slot : Nat) (ptr : Data) (w : OWNER)
    (es : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (older : root ≠ a)
    (source : s.cells ⟨root,slot,[]⟩ = some
      (PV_THR2_Packet315SourceReturn.value ptr PV_THR2_Packet218ReturnData.allocator))
    (n : Nat) (bound : n ≤ 8) :
    advance (PV_LIB_A_FetchSubMachine10.step (PV_THR2_OwnInitExactReturnedCases.carrier C b)
      K P resources encode H values) n (PV_LIB_A_FetchSubMachine10.wrap
        ⟨⟨⟨.running (PV_LIB_A_WeakGuardBuild10.configuration types s a parents root slot ptr 0),w,es⟩,stack⟩,none⟩) =
      PV_LIB_A_FetchSubMachine10.wrap
        ⟨⟨⟨.running (PV_LIB_A_WeakGuardBuild10.configuration types s a parents root slot ptr n),w,es⟩,stack⟩,none⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [advance,ih (by omega),nonwaiting]
    · rw [PV_LIB_A_WeakGuardBuildRun10.corrected_step C K b P resources encode H values
        types s a parents root slot ptr w es stack older source n (by omega)]
    · rfl

#print axioms advance
#print axioms nonwaiting
#print axioms guard_run
#print axioms build_run
end PV_LIB_A_FetchSubPrefixes10
