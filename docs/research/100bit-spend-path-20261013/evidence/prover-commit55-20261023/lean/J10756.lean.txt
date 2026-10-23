import R1Z.ProverCommitOracle55
import R1Z.ProverCommitSemanticInterpolation55
/-! Every partial-sum input is produced by the complete owned oracle. No
per-invocation oracle image, sample array image or round polynomial is assumed. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitOracleRounds55
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisR1.ExtractedCurrentQM31Exact (decode QM31Exact)
open ProverCommitTerminalZero55 (Statement publicModel)
open ProverCommitChallengePrefix55

theorem point_canonical (p : Nat → Old.Q) (hp : ∀ i, i<10 → Canonical (p i))
    (r : Fin 10) (a : Usize) (sample : U32) (hs : sample.val<28) :
    ∀ i, i<10 → Canonical (ProverCommitSamplePoint49.point p r.val a sample i) := by
  intro i hi
  rw [ProverCommitSamplePoint49.point,ProverCommitSampleTail49.values_at]
  split
  · unfold ProverCommitSampleTail49.qbit
    split
    · exact ProverCommitSubtraction47.one_canonical
    · exact zero_canonical
  · by_cases he : i=r.val
    · rw [he,Function.update_self]
      exact ProverCommitSamplePoint49.word_canonical sample hs
    · rw [Function.update_of_ne he]
      exact hp i hi

attribute [local irreducible] ProverCommitQBasis51.basis ProverCommitClaims53.trace
  ProverCommitTerminalZero55.publicModel ProverCommitSemanticModel55.oracle
  ProverCommitSamplePoint49.point ProverCommitNativeQ48.source ProverCommitQArray48.array

theorem exact_result (s : Statement) (sem p : Nat → Old.Q)
    (hs : ∀ i, i<25 → Canonical (sem i)) (hp : ∀ i, i<10 → Canonical (p i))
    (c : Nat → Nat → Old.Q) (hc : ∀ l, l<29 → ∀ i, i<1024 → Canonical (c l i))
    (template : R0Z.HonestView.Challenges QM31Exact) (r : Fin 10) (hprefix : Prefix sem p r.val)
    (words : Fin 512 → Usize) (hw : ∀ a, (words a).val=a.val)
    (sample : Fin 28 → U32) (hsample : ∀ t, (sample t).val=t.val)
    (left : U16) (hleft : left.val=2^(9-r.val))
    {H : Type} (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (hash : H) (c1 : Array U8 32#usize)
    (transcript : AspisR1PublicPreparation.r1_wire.SemanticTranscript H)
    (hprep : AspisR1PublicPreparation.r1_semantic.public_transcript D
      (AspisR1PublicPreparation.PreparationBinding.preparationPublic s) hash c1=ok (.Ok transcript)) :
    ∃ oracle : Nat → Nat → Old.Q, ∃ sums ys : Nat → Old.Q,
      (∀ (t : Fin 28) (a : Fin 512),
        ProverCommitOracle55.run s sem (ProverCommitSamplePoint49.point p r.val (words a) (sample t)) c=
          ok (.Ok (ProverCommitNativeQ48.source (oracle t.val a.val)))) ∧
      (∀ t, t<28 → ∀ a, a<512 → Canonical (oracle t a)) ∧
      (∀ t : Fin 28, owned.sum (ProverCommitQArray48.array 512#usize (oracle t.val)) 0#usize left
        (ProverCommitNativeQ48.source zero)=ok (ProverCommitNativeQ48.source (sums t.val))) ∧
      interpolate (ProverCommitQArray48.array 28#usize sums)=
        ok (ProverCommitQArray48.array 28#usize ys) ∧
      (∀ k, k<28 → Canonical (ys k)) ∧
      ProverCommitInterpolationRow48.qpoly ys=R0Z.PayloadSplit.rounds (withSemantic template sem) r
        (ProverCommitSemanticModel55.oracle AspisR1.rowEquiv (publicModel s) ProverCommitQBasis51.basis
          (withSemantic template sem) (ProverCommitClaims53.trace c)) := by
  have hone (t : Fin 28) (a : Fin 512) := ProverCommitOracle55.exact_result s sem
    (ProverCommitSamplePoint49.point p r.val (words a) (sample t)) hs
    (point_canonical p hp r (words a) (sample t) (by rw [hsample];exact t.isLt))
    c hc template D hash c1 transcript hprep
  choose out hout hcan hvalue using hone
  let oracle : Nat → Nat → Old.Q := fun t a =>
    if ht : t<28 then if ha : a<512 then out ⟨t,ht⟩ ⟨a,ha⟩ else zero else zero
  have ho (t : Fin 28) (a : Fin 512) : oracle t.val a.val=out t a := by
    simp only [oracle,dif_pos t.isLt,dif_pos a.isLt]
  have hcanon : ∀ t, t<28 → ∀ a, a<512 → Canonical (oracle t a) := by
    intro t ht a ha
    rw [ho ⟨t,ht⟩ ⟨a,ha⟩]
    exact hcan _ _
  have hbound : 2^(9-r.val)≤512 := by
    exact Nat.pow_le_pow_right (by decide : 1≤2) (show 9-r.val≤9 by omega)
  let smallWords : Fin (2^(9-r.val)) → Usize := fun a => words (Fin.castLE hbound a)
  obtain ⟨sums,ys,hsums,hcsums,hinter,hcys,hpoly⟩ :=
    ProverCommitSemanticInterpolation55.exact_result (withSemantic template sem) p r
      (model_prefix template sem p r hprefix) smallWords (fun a => hw (Fin.castLE hbound a))
      sample hsample left hleft oracle hcanon
      (ProverCommitSemanticModel55.oracle AspisR1.rowEquiv (publicModel s) ProverCommitQBasis51.basis
        (withSemantic template sem) (ProverCommitClaims53.trace c)) (by
          intro t a
          have he := ho t (Fin.castLE hbound a)
          change oracle t.val a.val=out t (Fin.castLE hbound a) at he
          rw [he]
          exact hvalue t (Fin.castLE hbound a))
  refine ⟨oracle,sums,ys,?_,hcanon,hsums,hinter,hcys,hpoly⟩
  intro t a
  rw [ho]
  exact hout t a

#print axioms point_canonical
#print axioms exact_result
end R1Z.ProverCommitOracleRounds55
