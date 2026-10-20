import CuSavingsS2SourceKernel
set_option autoImplicit false
namespace AspisR1.CuSavingsS2Candidate3
open Aeneas Aeneas.Std Result AspisR1S2Groups
open CuSavingsS2SourceArrays CuSavingsS2SourceCommon
variable [Shared]

/-- Unconditional equality of the complete emitted parent and candidate helper,
including malformed input, failing shared operations and divergence. -/
theorem helper_equivalence (w : Weights) (f : Slice U8) (low : Array E 16#usize) :
    new.grouped_inactive_pair w f low = old.grouped_inactive_pair w f low := by
  unfold new.grouped_inactive_pair
  rw [variant_eq]
  simp only [bind_tc_ok]
  by_cases hw : w.variant=transport.Variant.S2
  · simp only [hw,decide_true,↓reduceIte,size_product,bind_tc_ok]
    dsimp only
    by_cases hl : Slice.len f=2048#usize
    · simp only [hl,↓reduceIte]
      exact CuSavingsS2SourceKernel.source_kernel w f low hw hl
    · simp only [hl,↓reduceIte,fallback0,fallback1]
      rfl
  · simp only [hw,decide_false,↓reduceIte,fallback2,fallback3]
    rfl

/-- Extensional substitution in every unchanged computational caller context.
This is not a claim of separately re-extracted transaction bodies. -/
theorem all_callers_equivalence {A : Type}
    (context : (Weights → Slice U8 → Array E 16#usize → Result E) → A) :
    context new.grouped_inactive_pair = context old.grouped_inactive_pair := by
  have h : new.grouped_inactive_pair = old.grouped_inactive_pair := by
    funext w f low
    exact helper_equivalence w f low
  rw [h]

#print axioms helper_equivalence
#print axioms all_callers_equivalence
end AspisR1.CuSavingsS2Candidate3
