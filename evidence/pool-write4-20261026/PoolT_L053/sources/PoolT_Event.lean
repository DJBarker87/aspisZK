import PoolT_CopyShape
import PoolT_Canonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolT_Event
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open S2W_TrustedStd S2W_WrapperLaws S2W_ReturnedCheckpoint S2W_EntryWriteHistory
open MultiproofConeCanonical Hist_Store Hist_RuntimeEntry

/-- Invert the actual existing local committed writer event. Neither native
acceptance, writer key, copied payload nor post-heap equality is supplied
independently. This does not instantiate external runtime/history admission. -/
theorem verifier {A : Type} (native : S2W_ExtractionBoundary.First)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A)
    (program : S2W_ExtractionBoundary.Program) (before after : Store) (layout : Layout)
    (data : Slice U8) (state : A) (key : Nat)
    (image : AspisV8R19.DuplexFrames.Bytes)
    (committed : Hiq_NativeWriter.apply native copy allocator program before layout data state =
      (after,.committedWrite key image)) :
    ∃ saved post final,
      first native copy allocator (load before layout) program data state = ok (.Ok (saved,post,final)) ∧
      key = (layout.handles 2).1 ∧ image = bytesOf saved.val ∧
      after = commit before (layout.handles 2).1 saved ∧
      payloadBytes encode (post.payload (layout.handles 2).1) saved.val.length = image := by
  unfold Hiq_NativeWriter.apply at committed
  cases h : first native copy allocator (load before layout) program data state with
  | fail error => simp only [h] at committed; cases committed
  | div => simp only [h] at committed; cases committed
  | ok reply => cases reply with
    | Err error => simp only [h] at committed; cases committed
    | Ok value =>
      rcases value with ⟨saved,post,final⟩
      simp only [h] at committed
      have eqs := Prod.mk.inj committed
      have event := S2X.AccountEvent.committedWrite.inj eqs.2
      refine ⟨saved,post,final,rfl,event.1.symm,event.2.symm,eqs.1.symm,?_⟩
      rw [← event.2]
      exact PoolT_CopyShape.accepted_bytes native copy std allocator (load before layout)
        program data state final saved post h

#print axioms verifier
end AspisR1.PoolT_Event
end
