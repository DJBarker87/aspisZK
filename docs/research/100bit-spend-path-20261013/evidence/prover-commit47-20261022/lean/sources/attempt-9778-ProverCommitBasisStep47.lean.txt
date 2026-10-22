import R1Z.ProverCommitBasisFillValue47
import R1Z.ProverCommitBasisMath47
/-! One symbolic power-of-two basis block and next factor. -/
set_option autoImplicit false
namespace R1Z.ProverCommitBasisStep47
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open ProverCommitPairCounter47 ProverCommitBasisCounter47 ProverCommitBasisFillValue47
open AspisR1.ExtractedCurrentQM31Exact AspisCircleTensorBinding
attribute [local irreducible] sourceArray fillN

theorem cast_width (width : Usize) (hwidth : width.val≤256) :
    (UScalar.cast .U16 width).val=width.val := by
  apply UScalar.cast_val_mod_pow_of_inBounds_eq
  change width.val<65536
  omega

theorem step (x : QM31Exact) (depth : Nat) (width : Usize)
    (hw : width.val=2^depth) (capacity : 2*width.val≤512)
    (xs : Nat → Old.Q) (hxs : ∀ k, k<512 → Canonical (xs k))
    (hvalues : ∀ k, k<width.val → decode (xs k)=naturalLineValue x k)
    (factor : Old.Q) (hcf : Canonical factor) (hfactor : decode factor=doubledFactor x depth) :
    ∃ (ys : Nat → Old.Q) (next : Old.Q),
      fill (sourceArray 512#usize xs) 0#usize (UScalar.cast .U16 width) width
        (ProverCommitNativeOps47.embedded factor)=ok (sourceArray 512#usize ys) ∧
      ProverCommitSubtraction47.double (ProverCommitNativeOps47.embedded factor)=
        ok (ProverCommitNativeOps47.embedded next) ∧
      (∀ k, k<512 → Canonical (ys k)) ∧ Canonical next ∧
      (∀ k, k<2*width.val → decode (ys k)=naturalLineValue x k) ∧
      decode next=doubledFactor x (depth+1) := by
  obtain ⟨ys,hy,hcy,hyval⟩ := fill_value width.val xs hxs 0#usize width
    (by change 0+width.val≤width.val;omega) capacity factor hcf
  obtain ⟨next,hn,hcn,hnval⟩ := ProverCommitSubtraction47.double_exact factor hcf
  refine ⟨ys,next,?_,hn,hcy,hcn,?_,?_⟩
  · rw [fill_source width.val _ (cast_width width (by omega))]
    exact hy
  · intro k hk
    rw [hyval k (by omega)]
    change (if width.val+0≤k ∧ k<width.val+0+width.val then
      decode (xs (k-width.val))*decode factor else decode (xs k)) = _
    by_cases hl : k<width.val
    · rw [if_neg (by omega)]
      exact hvalues k hl
    · rw [if_pos (by omega),hvalues (k-width.val) (by omega),hfactor]
      have hb : k-width.val<2^depth := by rw [← hw];omega
      have hindex : 2^depth+(k-width.val)=k := by rw [← hw];omega
      rw [← ProverCommitBasisMath47.block depth x (k-width.val) hb,hindex]
  · rw [hnval,hfactor]
    rfl

#print axioms cast_width
#print axioms step
end R1Z.ProverCommitBasisStep47
