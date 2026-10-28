import R1Z.ProverRwDictionaryMerkle
import R1Z.ProverCommitWideQM31Scalar49
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwDictionaryWideQM
open Aeneas Aeneas.Std Result ProverRwFull ProverRwDictionaryTower
open ProverCommitWideOps48
open AspisR1.ExtractedCurrentQM31Exact (decode)
variable [ExternalTypes]

def mul (a : W) (b : Q) : Result W := mapResult fromW
  (AspisR1ProducerRelease47.field.wide_exact.WideExact.mul_qm31 (toW a) (toQ b))
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {ProverRwDictionaryMerkle.selected ops with op48 := mul}

theorem installed (ops : ExternalFuns) (a : W) (b : Q) :
    (selected ops).op48 a b = mul a b := rfl

/-- No canonical-rhs premise is needed: the actual callee normalizes it. -/
theorem correct (ops : ExternalFuns) (x : Raw) (q : ProverCommitPrimitive47.Old.Q)
    (hx : canonical x) :
    ∃ z : Raw,
      (selected ops).op48 (fromW (source x)) (fromQ (ProverCommitNativeQ48.source q)) =
        .ok (fromW (source z)) ∧ canonical z ∧
      value z = value x * ProverCommitWideQM31Scalar49.embed (decode q) := by
  obtain ⟨z,hz,hc,hd⟩ := ProverCommitWideQM31Scalar49.value_exact x q hx
  refine ⟨z,?_,hc,hd⟩
  rw [installed]
  unfold mul
  rw [native_w_roundtrip,native_q_roundtrip,hz]
  rfl

#print axioms installed
#print axioms correct
end R1Z.ProverRwDictionaryWideQM
