import R1Z.ProverCommitSemanticInterpolation55
import R1Z.ProverCommitSemanticRounds55
import R1Z.ProverCommitFinalShift49
/-! Source partial sums, interpolation, actual half/inverse producer and
final two-coefficient shift compose to the model's entire round-9 polynomial.
Per-oracle call, input terminal and challenge provenance stay explicit. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitSemanticFinal55
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisR1.ExtractedCurrentQM31Exact (decode QM31Exact)
open R0P R0P.SemSource R0Z.HonestView R0Z.PayloadSplit R0Z.Shift R0Z.RefPayload
open ProverCommitInterpolationRow48 Polynomial
variable {F : Subfield QM31Exact} {Bat : Type} [BatchedLayer QM31Exact Bat]

theorem poly_eq_qpoly (v : Nat → Old.Q) :
    ProverCommitInterpolationPoly48.poly 28 (fun k => decode (v k))=qpoly v := rfl

attribute [local irreducible] qpoly ProverCommitQArray48.array ProverCommitNativeQ48.source

theorem exact_result (pi : Fin 1024 ≃ Fin 1024) (pub : Public QM31Exact) (B : PackBasis F)
    (ch : Challenges QM31Exact) (t : Trace QM31Exact) (p : Nat → Old.Q)
    (hprefix : ∀ i : Fin 10, i.val<9 → decode (p i.val)=alpha ch i)
    (words : Fin (2^(9-(9 : Fin 10).val)) → Usize) (hw : ∀ a, (words a).val=a.val)
    (sample : Fin 28 → U32) (hsample : ∀ s, (sample s).val=s.val)
    (left : U16) (hleft : left.val=2^(9-(9 : Fin 10).val))
    (calls : Nat → Nat → Old.Q)
    (hcanonical : ∀ s, s<28 → ∀ a, a<512 → Canonical (calls s a))
    (horacle : ∀ (s : Fin 28) (a : Fin (2^(9-(9 : Fin 10).val))),
      decode (calls s.val a.val)=ProverCommitSemanticModel55.oracle pi pub B ch t (fun i : Fin 10 =>
        decode (ProverCommitSamplePoint49.point p 9 (words a) (sample s) i.val)))
    (a original eta0 : Old.Q) (ha : Canonical a) (ho : Canonical original) (he : Canonical eta0)
    (haval : decode a=alpha ch 9)
    (ho_image : decode original=fOrig pub B ch t (alpha ch))
    (he_image : decode eta0=fOrig pub B ch 0 (alpha ch))
    (hhalf : alpha ch 9≠1/2) :
    ∃ sums ys out : Nat → Old.Q,
      (∀ s : Fin 28, owned.sum (ProverCommitQArray48.array 512#usize (calls s.val)) 0#usize left
        (ProverCommitNativeQ48.source zero)=ok (ProverCommitNativeQ48.source (sums s.val))) ∧
      interpolate (ProverCommitQArray48.array 28#usize sums)=ok (ProverCommitQArray48.array 28#usize ys) ∧
      ProverCommitFinalShift49.run (ProverCommitQArray48.array 28#usize ys) (ProverCommitNativeQ48.source a)
        (ProverCommitNativeQ48.source original) (ProverCommitNativeQ48.source eta0)=
          ok (some (ProverCommitQArray48.array 28#usize out)) ∧
      (∀ k, k<28 → Canonical (out k)) ∧
      qpoly out=R0Z.Chain.roundPoly 9
        (shift pub B ch (refPayload (Bat := Bat) pub B ch+L pi B ch t)) := by
  obtain ⟨sums,ys,hsums,hcsums,hys,hcys,hdys⟩ := ProverCommitSemanticInterpolation55.exact_result
    ch p 9 hprefix words hw sample hsample left hleft calls hcanonical
    (ProverCommitSemanticModel55.oracle pi pub B ch t) horacle
  have hn : decode a≠(2 : QM31Exact)⁻¹ := by
    rw [haval]
    simpa only [one_div] using hhalf
  obtain ⟨out,hout,hcout,hdout⟩ := ProverCommitFinalShift49.exact_result ys hcys a original eta0 ha ho he hn
  refine ⟨sums,ys,out,hsums,hys,hout,hcout,?_⟩
  rw [poly_eq_qpoly out,poly_eq_qpoly ys] at hdout
  rw [hdout,hdys,ho_image,he_image,haval,ProverCommitSemanticRounds55.payload_rounds,if_pos rfl]
  simp only [one_div]

#print axioms poly_eq_qpoly
#print axioms exact_result
end R1Z.ProverCommitSemanticFinal55
