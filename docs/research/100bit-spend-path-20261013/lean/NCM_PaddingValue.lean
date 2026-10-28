import NCM_PaddingBytes

set_option autoImplicit false
noncomputable section
namespace AspisR1.NCM_PaddingValue
open Aeneas Aeneas.Std Result NCE_PaddingCuts

/-- Actual iterator's complete-word zero test is exactly the original suffix
zero test; there is no hidden successful-padding premise. -/
theorem chunks_zero (padding : Slice U8) (ce : Iter)
    (constructed : core.slice.Slice.chunks_exact padding 8#usize = ok ce)
    (whole : padding.val.length%8 = 0) :
    NCM_PaddingScan.allZero ce.chunks = padding.val.all (fun b => b == 0#u8) := by
  have equivalent : NCM_PaddingScan.allZero ce.chunks = true ↔ padding.val.all (fun b => b == 0#u8) = true := by
    simp only [NCM_PaddingScan.allZero,List.all_eq_true,beq_iff_eq]
    exact NCM_PaddingCover.zero padding ce constructed whole
  cases left : NCM_PaddingScan.allZero ce.chunks <;>
    cases right : padding.val.all (fun b => b == 0#u8) <;>
    simp_all only [Bool.false_eq_true,not_false_eq_true,iff_false,iff_true,not_true_eq_false]

/-- Complete native loop result is derived from ONE-step cuts on the actual
partition, with the returned first-stop iterator and caller frame retained. -/
theorem observation {Frame : Type} (base : Port3_NativeBatchBody.Ops) {X : Type}
    (D : AspisR1Stage2.aspis_core.digest.Digest32 X) (native : Body Frame)
    (cut : NCE_Native_Padding (NCM_PaddingPredicate.predicate base D) native)
    (padding : Slice U8) (words : Nat) (length : padding.val.length = 8*words) (frame : Frame) :
    ∃ ce after, core.slice.Slice.chunks_exact padding 8#usize = ok ce ∧
      run native (ce.chunks.length+1) (ce,frame) =
        ok (!MultiproofConePadding.scan words (MultiproofConeCanonical.bytesOf padding.val),after,frame) := by
  obtain ⟨ce,constructed,runEq⟩ := NCE_PaddingPhysical.physical_run (NCM_PaddingPredicate.predicate base D) native cut padding frame
  obtain ⟨after,returned⟩ := NCM_PaddingScan.native_value base D native cut ce.chunks ce.remainder frame
    (NCE_PaddingPhysical.chunk_sizes padding ce constructed)
  refine ⟨ce,after,constructed,?_⟩
  rw [chunks_zero padding ce constructed (by omega),←NCM_PaddingBytes.scan padding words length] at returned
  exact returned

#print axioms chunks_zero
#print axioms observation
end AspisR1.NCM_PaddingValue
end
