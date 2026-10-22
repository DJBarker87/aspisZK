import R1Z.ProverCommitCoefficientModel51
import R1Z.ProverCommitExtraClaim51
/-! Coefficient producer followed by the actual reverse-Horner extra owner. -/
set_option autoImplicit false
namespace R1Z.ProverCommitExtraCaller51
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisR1.ExtractedCurrentQM31Exact (decode QM31Exact)

theorem source_array (q : Nat → Old.Q) :
    ProverCommitQArray48.array 1024#usize q=ProverCommitExtra48.sourceArray q := rfl

def run (rows : Array field.QM31 1024#usize) (a b : field.QM31) : Result field.QM31 := do
  let coefficients ← coefficients51.eval rows
  extra coefficients a b

attribute [local irreducible] ProverCommitQArray48.array ProverCommitExtra48.sourceArray ProverCommitNativeQ48.source
  coefficients51.eval extra

theorem exact_result (rows p : Nat → Old.Q)
    (hr : ∀ j, j<1024 → Canonical (rows j)) (hp : ∀ i, i<10 → Canonical (p i))
    (t : R0P.Trace QM31Exact) (ht : ∀ j : Fin 1024, decode (rows j.val)=t 28 j) :
    ∃ z : Old.Q, run (ProverCommitQArray48.array 1024#usize rows)
      (ProverCommitNativeQ48.source (p 8)) (ProverCommitNativeQ48.source (p 9))=
        ok (ProverCommitNativeQ48.source z) ∧ Canonical z ∧
      decode z=R0P.Mask.honestExtra AspisR1.rowEquiv t (fun i : Fin 10 => decode (p i.val)) 28 := by
  obtain ⟨q,hq,hcq,hdq⟩ := ProverCommitCoefficientModel51.exact_result rows hr t 28 ht
  obtain ⟨z,hz,hcz,hdz⟩ := ProverCommitExtraClaim51.exact_result q hcq p hp AspisR1.rowEquiv t hdq
  refine ⟨z,?_,hcz,hdz⟩
  rw [run,hq]
  simp only [bind_tc_ok,source_array]
  exact hz

#print axioms source_array
#print axioms exact_result
end R1Z.ProverCommitExtraCaller51
