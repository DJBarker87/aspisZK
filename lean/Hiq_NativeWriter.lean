import Hiq_RuntimeWriter
import S2W_D189Wrappers
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hiq_NativeWriter
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry S2Trust S2W_D189Entry S2W_D189Wrappers

/-- The ledger effect is chosen from the ACTUAL complete native-wrapper
reply, including allocator/copy/cleanup failure. All failed transactions roll
back under the existing runtime semantics. -/
def apply {A : Type} (native : S2W_ExtractionBoundary.First)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (store : Store)
    (layout : Layout) (data : Slice U8) (state : A) : Store × S2X.AccountEvent :=
  match first native copy allocator (load store layout) id data state with
  | .ok (.Ok (saved,_,_)) => (commit store (layout.handles 2).1 saved,
      .committedWrite (layout.handles 2).1 (MultiproofConeCanonical.bytesOf saved.val))
  | _ => (store,.rollback)

theorem classified {A : Type} (ops : AdapterRw.Ops) (law : ops.op36 = Hist_Authority.keyEq)
    (native : S2W_ExtractionBoundary.First)
    (source : ∀ id accounts data, AdapterRw.r1_pool_adapter.owned.stage1_owned ops id accounts data = native id accounts data)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (trustedCopy : S2W_TrustedStd.TrustedStd copy) (allocator : Allocator A)
    (id : S2W_ExtractionBoundary.Program) (store : Store) (layout : Layout) (data : Slice U8) (state : A) :
    Step ops id store (apply native copy allocator id store layout data state).2
      (apply native copy allocator id store layout data state).1 := by
  unfold apply
  cases h : first native copy allocator (load store layout) id data state with
  | fail e => exact Step.rollback store
  | div => exact Step.rollback store
  | ok reply => cases reply with
    | Err e => exact Step.rollback store
    | Ok value =>
      rcases value with ⟨saved,post,final⟩
      have accepted := (first_accepted native copy trustedCopy allocator (load store layout) id data state final saved post h).1
      have sourceAccepted := (source id (load store layout).first data).trans accepted
      exact Step.first store (layout.handles 2).1 (load store layout) data saved rfl
        (Hiq_KeyLaw.owner ops law id store layout data saved sourceAccepted) sourceAccepted

#print axioms classified
end AspisR1.Hiq_NativeWriter
end
