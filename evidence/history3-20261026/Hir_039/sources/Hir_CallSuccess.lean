import Hir_SelectedOrigin
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hir_CallSuccess
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call Hir_Schedule Hir_ProvenanceModel

theorem effect {A : Type}
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (store : Store) (call : Call A)
    (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record)) (final : A)
    (route : Hiq_ReleaseRoute.route call.data = .first)
    (accepted : first native1 copy allocator (load store call.layout) id call.data call.state = ok (.Ok (saved,post,final))) :
    Hir_Call.native native1 native2 copy allocator id store call =
      (commit store (call.layout.handles 2).1 saved,
        .committedWrite (call.layout.handles 2).1 (MultiproofConeCanonical.bytesOf saved.val),
        .inl (.ok (.Ok (saved,post,final)))) := by
  simp only [Hir_Call.native,route,firstEffect,accepted]

#print axioms effect
end AspisR1.Hir_CallSuccess
end
