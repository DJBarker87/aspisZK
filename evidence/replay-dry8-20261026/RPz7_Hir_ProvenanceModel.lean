import RPz7_Hir_FactoryCharge
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hir_ProvenanceModel
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call Hir_Schedule
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

def Zero (data : Slice U8) : Prop := ∀ byte ∈ data.val, byte = 0#u8

/-- Solana's account-owner assignment rule: changing owner requires zero data.
This is runtime account semantics, not a Pool or verifier source law. It is
NOT supplied by the older unrestricted foreign-write projection. -/
def Assignable (store : Store) (key : Nat) (value : Cell) : Prop :=
  value.owner = (store key).owner ∨ Zero value.data

structure CallAt (A : Type) where
  before : Store
  call : Call A

variable {A B : Type}
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)

def calls (H : Bytes → State) (store : Store) : Schedule A B → List (CallAt A)
  | .done _ => []
  | .inspect k => calls H store (k store)
  | .ask query k => calls H store (k (H query))
  | .invoke call k =>
    let head := Hir_Call.native native1 native2 copy allocator id store call
    ⟨store,call⟩ :: calls H head.1 (k head.2.2)
  | .foreign caller key value k =>
    let head := Hiq_NativeAction.apply native1 copy allocator id store (.foreign caller key value)
    calls H head.1 (k head.2)
  | .rollback k => calls H store k

def admissible (H : Bytes → State) (store : Store) : Schedule A B → Prop
  | .done _ => True
  | .inspect k => admissible H store (k store)
  | .ask query k => admissible H store (k (H query))
  | .invoke call k =>
    let head := Hir_Call.native native1 native2 copy allocator id store call
    admissible H head.1 (k head.2.2)
  | .foreign caller key value k =>
    let head := Hiq_NativeAction.apply native1 copy allocator id store (.foreign caller key value)
    (head.2 = .rollback ∨ Assignable store key value) ∧ admissible H head.1 (k head.2)
  | .rollback k => admissible H store k

/-- A concrete successful whole native TX1 in the measured schedule, on the
same physical key and the exact final selected data. -/
def Birth (key : Nat) (data : Slice U8) (site : CallAt A) : Prop :=
  Hiq_ReleaseRoute.route site.call.data = .first ∧ (site.call.layout.handles 2).1 = key ∧
    ∃ saved post final,
      first native1 copy allocator (load site.before site.call.layout) id site.call.data site.call.state =
        ok (.Ok (saved,post,final)) ∧ data = saved.deref

end AspisR1.Hir_ProvenanceModel
end
