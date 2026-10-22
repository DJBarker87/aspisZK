import R1Z.ProverCommitBasisStep47
/-! Full nine-stage value theorem for the structurally recursive basis owner.
This does not assert the unproved native-loop/source-owner connection. -/
set_option autoImplicit false
namespace R1Z.ProverCommitBasisValue47
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open ProverCommitPairCounter47 ProverCommitBasisCounter47 ProverCommitBasisStep47
open AspisR1.ExtractedCurrentQM31Exact AspisCircleTensorBinding
attribute [local irreducible] sourceArray stagesN naturalLineValue doubledFactor

theorem stages_step (n : Nat) (out : Array field.wide_exact.WideExact 512#usize)
    (width : Usize) (factor : field.wide_exact.WideExact) :
    stagesN (n+1) out width factor =
      (do let out ← fill out 0#usize (UScalar.cast .U16 width) width factor
          let next ← ProverCommitSubtraction47.double factor
          stagesN n out (Usize.wrapping_mul width 2#usize) next) := by
  simp only [stagesN,ProverCommitSubtraction47.double,bind_assoc]

theorem stages_value (n depth : Nat) (room : depth+n≤9) (x : QM31Exact)
    (width : Usize) (hw : width.val=2^depth)
    (xs : Nat → Old.Q) (hxs : ∀ k, k<512 → Canonical (xs k))
    (hvalues : ∀ k, k<width.val → decode (xs k)=naturalLineValue x k)
    (factor : Old.Q) (hcf : Canonical factor) (hfactor : decode factor=doubledFactor x depth) :
    ∃ ys : Nat → Old.Q,
      stagesN n (sourceArray 512#usize xs) width (ProverCommitNativeOps47.embedded factor)=
        ok (sourceArray 512#usize ys) ∧
      (∀ k, k<512 → Canonical (ys k)) ∧
      ∀ k, k<2^(depth+n) → decode (ys k)=naturalLineValue x k := by
  induction n generalizing depth width xs factor with
  | zero =>
    refine ⟨xs,by rw [stagesN],hxs,?_⟩
    intro k hk
    exact hvalues k (by simpa only [Nat.add_zero,← hw] using hk)
  | succ n ih =>
    have cap : 2*width.val≤512 := by
      have hp : 2^(depth+1)≤2^9 := Nat.pow_le_pow_right (by decide) (by omega)
      rw [pow_succ] at hp
      norm_num at hp
      rw [hw]
      omega
    obtain ⟨nextValues,nextFactor,hfill,hdouble,hcvalues,hcfactor,hv,hf⟩ :=
      step x depth width hw cap xs hxs hvalues factor hcf hfactor
    have hnext : (Usize.wrapping_mul width 2#usize).val=2^(depth+1) := by
      rw [Usize.wrapping_mul_val_eq]
      have two : (2#usize).val=2 := by scalar_tac
      rw [two,Nat.mod_eq_of_lt (by have := usize_large;omega),hw,pow_succ]
    have hvnext : ∀ k, k<(Usize.wrapping_mul width 2#usize).val →
        decode (nextValues k)=naturalLineValue x k := by
      intro k hk
      apply hv k
      rw [hnext,pow_succ,← hw] at hk
      omega
    obtain ⟨ys,hy,hcy,hyv⟩ := ih (depth+1) (by omega) (Usize.wrapping_mul width 2#usize)
      hnext nextValues hcvalues hvnext nextFactor hcfactor hf
    refine ⟨ys,?_,hcy,?_⟩
    · rw [stages_step,hfill]
      simp only [bind_tc_ok]
      rw [hdouble]
      exact hy
    · have hi : depth+1+n=depth+(n+1) := by omega
      simpa only [hi] using hyv

/-- Canonicality and exact natural-basis values at all 512 positions, with
no native basis-value or source-success premise. This certifies the owned
reference; the actual shipped basis::values loop still needs its binding. -/
theorem values_exact (x : Old.Q) (hx : Canonical x) :
    ∃ ys : Nat → Old.Q,
      values (ProverCommitNativeOps47.embedded x)=ok (sourceArray 512#usize ys) ∧
      (∀ k, k<512 → Canonical (ys k)) ∧
      ∀ k, k<512 → decode (ys k)=naturalLineValue (decode x) k := by
  have start : ∀ k, k<(1#usize).val →
      decode ((fun _ => ProverCommitSubtraction47.one) k)=naturalLineValue (decode x) k := by
    intro k hk
    have hz : k=0 := by change k<1 at hk;omega
    rw [hz,ProverCommitSubtraction47.one_decode,ProverCommitBasisMath47.natural_zero]
  obtain ⟨ys,hy,hcy,hyv⟩ := stages_value 9 0 (by decide) (decode x) 1#usize rfl
    (fun _ => ProverCommitSubtraction47.one) (fun _ _ => ProverCommitSubtraction47.one_canonical)
    start x hx (by rw [doubledFactor])
  refine ⟨ys,?_,hcy,?_⟩
  · rw [values_counter,ProverCommitArrayValue47.ones]
    exact hy
  · exact hyv

#print axioms stages_step
#print axioms stages_value
#print axioms values_exact
end R1Z.ProverCommitBasisValue47
