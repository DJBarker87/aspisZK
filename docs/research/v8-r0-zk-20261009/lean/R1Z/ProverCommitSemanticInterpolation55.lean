import R1Z.ProverCommitSampleSum49
import R1Z.ProverCommitSampleModel49
import R1Z.ProverCommitInterpolationModel48
import R0Z.PayloadSplit
/-! Compose every owned partial sum with the complete interpolation producer.
The remaining provenance is per oracle invocation at the actual source point,
not an assumed polynomial or sample-sum array image. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitSemanticInterpolation55
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisR1.ExtractedCurrentQM31Exact (decode QM31Exact)
open R0Z.HonestView
open scoped BigOperators

theorem exact_result (ch : Challenges QM31Exact) (p : Nat → Old.Q) (r : Fin 10)
    (hprefix : ∀ i : Fin 10, i.val<r.val → decode (p i.val)=alpha ch i)
    (words : Fin (2^(9-r.val)) → Usize) (hw : ∀ a, (words a).val=a.val)
    (sample : Fin 28 → U32) (hsample : ∀ s, (sample s).val=s.val)
    (left : U16) (hleft : left.val=2^(9-r.val))
    (oracle : Nat → Nat → Old.Q)
    (hcanonical : ∀ s, s<28 → ∀ a, a<512 → Canonical (oracle s a))
    (f : (Fin 10 → QM31Exact) → QM31Exact)
    (horacle : ∀ (s : Fin 28) (a : Fin (2^(9-r.val))),
      decode (oracle s.val a.val)=f (fun i : Fin 10 =>
        decode (ProverCommitSamplePoint49.point p r.val (words a) (sample s) i.val))) :
    ∃ sums ys : Nat → Old.Q,
      (∀ s : Fin 28, owned.sum (ProverCommitQArray48.array 512#usize (oracle s.val)) 0#usize left
        (ProverCommitNativeQ48.source zero)=ok (ProverCommitNativeQ48.source (sums s.val))) ∧
      (∀ s, s<28 → Canonical (sums s)) ∧
      interpolate (ProverCommitQArray48.array 28#usize sums)=ok (ProverCommitQArray48.array 28#usize ys) ∧
      (∀ k, k<28 → Canonical (ys k)) ∧
      ProverCommitInterpolationRow48.qpoly ys=R0Z.PayloadSplit.rounds ch r f := by
  have hbound : 2^(9-r.val)≤512 := by
    have h := Nat.pow_le_pow_right (by decide : 1≤2) (show 9-r.val≤9 by omega)
    exact h
  have hsum : ∀ s : Fin 28, ∃ z : Old.Q,
      owned.sum (ProverCommitQArray48.array 512#usize (oracle s.val)) 0#usize left
        (ProverCommitNativeQ48.source zero)=ok (ProverCommitNativeQ48.source z) ∧
      Canonical z ∧ decode z=∑ b : Fin (9-r.val) → Bool,
        f (roundPoint ch r (s.val : QM31Exact) b) := by
    intro s
    obtain ⟨z,hz,hcz,hdz⟩ := ProverCommitSampleSum49.partial_sum (oracle s.val)
      (hcanonical s.val s.isLt) (2^(9-r.val)) hbound left hleft
    refine ⟨z,hz,hcz,hdz.trans ?_⟩
    rw [←Fin.sum_univ_eq_sum_range (fun i => decode (oracle s.val i)) (2^(9-r.val))]
    calc
      _=∑ a : Fin (2^(9-r.val)), f (fun i : Fin 10 =>
          decode (ProverCommitSamplePoint49.point p r.val (words a) (sample s) i.val)) := by
        apply Finset.sum_congr rfl
        intro a ha
        exact horacle s a
      _=∑ b : Fin (9-r.val) → Bool, f (roundPoint ch r (s.val : QM31Exact) b) := by
        simpa only [hsample s] using ProverCommitSampleModel49.sum_points ch p r hprefix words hw (sample s) f
  choose zs hzs hczs hdzs using hsum
  let sums : Nat → Old.Q := fun s => if hs : s<28 then zs ⟨s,hs⟩ else zero
  have hsums (s : Fin 28) : sums s.val=zs s := by simp only [sums,dif_pos s.isLt]
  obtain ⟨ys,hy,hcy,hdy⟩ := ProverCommitInterpolationModel48.interpolate_model sums
  refine ⟨sums,ys,?_,?_,hy,hcy,?_⟩
  · intro s;rw [hsums];exact hzs s
  · intro s hs
    have := hczs (⟨s,hs⟩ : Fin 28)
    simpa only [sums,dif_pos hs] using this
  · rw [hdy,R0Z.PayloadSplit.rounds_apply]
    congr 1
    funext s
    rw [hsums]
    exact hdzs s

#print axioms exact_result
end R1Z.ProverCommitSemanticInterpolation55
