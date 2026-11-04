import NGK_COMBINED_IMPORT
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGR_HISTORY
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry
open AspisV8R19.DuplexFrames MultiproofConeCanonical

/-- Only source protection supplies the final data and funding; the runtime
law is not used to infer owner or lamport preservation. -/
theorem protected_image {Tx A : Type} (p : CPG_Projection.Observations Tx A)
    (t : Tx) (saved : alloc.vec.Vec U8) (id : S2W_ExtractionBoundary.Program)
    (protection : CPH_Protection.Facts p t saved id) :
    (CPG_Projection.tentative p t ((p.layout t).handles 2).1).data = bytesOf saved.val ∧
    (CPG_Projection.tentative p t ((p.layout t).handles 2).1).lamports ≠ 0 := by
  obtain ⟨_, _, positive, _, frame, funding⟩ := protection
  constructor
  · change bytesOf ((p.parentTentative t).cells ((p.layout t).handles 2).1).data.val = _
    rw [frame]
    exact CPR_SourceBank.copied_data _ _ saved
  · change (p.parentTentative t).lamports ((p.layout t).handles 2).1 ≠ 0
    omega

/-- Accepted RuntimePersistence, restricted to its data-only projection. The
conclusion is derived, never an input `persisted_bytes` equality. -/
theorem persisted_bytes {Tx A : Type} (p : CPG_Projection.Observations Tx A)
    (t u : Tx) (saved : alloc.vec.Vec U8) (id system : S2W_ExtractionBoundary.Program)
    (adjacent : CPG_Projection.adjacent p t u)
    (ordinary : CPG_Projection.ordinary p system t ((p.layout t).handles 2).1)
    (parent : CPG_Projection.success p t = true)
    (protection : CPH_Protection.Facts p t saved id)
    (RuntimePersistence : CPR_DataPersistence.TwoTransactionLaw
      (CPG_Projection.adjacent p) (CPG_Projection.ordinary p system)
      (CPG_Projection.before p) (CPG_Projection.tentative p)
      (CPG_Projection.success p) (CPG_Projection.loaded p)) :
    CPG_Projection.loaded p u ((p.layout t).handles 2).1 = some (bytesOf saved.val) := by
  obtain ⟨written,positive⟩ := protected_image p t saved id protection
  rw [RuntimePersistence t u adjacent _ ordinary, parent]
  simp only [if_true, CPR_DataPersistence.visible, positive, if_false, written]

/-- A successful data load implies a live account and identifies the exact
entry buffer. No runtime metadata equality is inferred. -/
theorem loaded_buffer {Tx A : Type} (p : CPG_Projection.Observations Tx A)
    (u : Tx) (key : Nat) (saved : alloc.vec.Vec U8)
    (loaded : CPG_Projection.loaded p u key = some (bytesOf saved.val)) :
    ((CPG_Projection.entry p u).buffers key).val = saved.val := by
  have positive : 0 < (p.bank u).lamports key := by
    by_contra h
    have zero : (p.bank u).lamports key = 0 := by omega
    change CPR_DataPersistence.visible (CPR_DataPersistence.snapshot (p.bank u) key) = _ at loaded
    simp only [CPR_DataPersistence.visible, CPR_DataPersistence.snapshot, zero, if_pos rfl] at loaded
    cases loaded
  have same := Option.some.inj ((CPG_Projection.live p u key positive).symm.trans loaded)
  exact MultiproofConeByteEquality.bytes_injective same

#print axioms protected_image
#print axioms persisted_bytes
#print axioms loaded_buffer
end AspisR1.NGR_HISTORY
end
