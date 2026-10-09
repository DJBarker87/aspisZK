import R0Z.ViewAffine

/-! A necessary identity for D11's proposed separated remainder, and the
mixed copy-residual term that obstructs it. The sparse row below represents
the row-12 contribution at a point supported on rows 12 and 13. Its source
instantiation is audited in LOG; this file does not unfold the copy registry,
enumerate rows, or claim a kernel-checked full-transcript counterexample. -/
set_option autoImplicit false
noncomputable section
namespace R0Z.D11Obstruction
open R0P

variable {F R E V : Type} [Field F]
  [AddCommGroup R] [Module F R] [AddCommGroup E] [Module F E]
  [AddCommGroup V] [Module F V]

/-- A joint linear map plus a remainder depending only on eligible noise
has no mixed difference between the two tape summands. -/
theorem separated_mixed_difference (c : V) (A : R × E →ₗ[F] V) (g : E → V)
    (r : R) (e : E) :
    (c + A (r,e) + g e) - (c + A (0,e) + g e) -
      (c + A (r,0) + g 0) + (c + A (0,0) + g 0) = 0 := by
  have he : (r,e) = (r,0) + (0,e) := by simp
  rw [he, map_add]
  rw [show A (0,0) = 0 from map_zero A]
  abel

variable {K : Type} [Field K]

/-- Exact active row-12 slot pattern after applying selector weight -1.
The other slots have no endpoint at either row in the sparse support. -/
def sparseRow (tag offset s : K) : CopyRowExtension K :=
  ⟨![ -(tag + offset + 2*s), 0 ], ![ -1, 0 ], ![0,0], ![0,0]⟩

/-- The active selector and the equality selector are both -1, so their
product is +1. The H1 opening changes by 2*h and the C1 opening by 2*s. -/
def sparseCopySlice (tag offset helper s h : K) : K :=
  copyResidual (sparseRow tag offset s) (helper + 2*h) 1

theorem sparse_copy_mixed_difference (tag offset helper s h : K) :
    sparseCopySlice tag offset helper s h - sparseCopySlice tag offset helper s 0 -
      sparseCopySlice tag offset helper 0 h + sparseCopySlice tag offset helper 0 0 =
        4*s*h := by
  simp [sparseCopySlice, sparseRow, copyResidual]
  ring

/-- The elementary copy slice cannot have the form mandated by D11 whenever
four is nonzero. The field-characteristic fact holds in the reference field. -/
theorem sparse_copy_not_separated (tag offset helper : K) (h4 : (4 : K) ≠ 0) :
    ¬ ∃ (c : K) (A : K × K →ₗ[K] K) (g : K → K),
      ∀ r e, sparseCopySlice tag offset helper e r = c + A (r,e) + g e := by
  rintro ⟨c,A,g,he⟩
  have hm := sparse_copy_mixed_difference tag offset helper 1 1
  simp only [he] at hm
  rw [separated_mixed_difference] at hm
  apply h4
  simpa only [mul_one] using hm.symm

#print axioms separated_mixed_difference
#print axioms sparse_copy_mixed_difference
#print axioms sparse_copy_not_separated
end R0Z.D11Obstruction
