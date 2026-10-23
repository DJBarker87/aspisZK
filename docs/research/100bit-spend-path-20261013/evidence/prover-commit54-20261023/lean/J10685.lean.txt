import R1Z.ProverCommitOpenedValues54
import R1Z.ProverCommitGammaCoefficients53
import R1Z.PhaseLeafEncodingBin
/-! Actual per-column coefficient Results and the entire retained opened matrix.
No coefficient-array or encoder/model image is supplied by the caller. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitOpenedModel54
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open ProverCommitWideOps48 ProverCommitMix48
open ProverCommitGammaCoefficients53 ProverCommitOpenedColumn54 ProverCommitOpenedValues54

attribute [local irreducible] value source sourceArray wideTrace symbol

theorem exact_result (c : Nat → Nat → Old.Q)
    (hc : ∀ l, l<29 → ∀ i, i<1024 → Canonical (c l i))
    (j : Usize) (u : Fin 262144) (hj : j.val=u.val) :
    ∃ out : Nat → Nat → Raw,
      leaves54.opened_values (coefficients (wide c hc)) j=ok (matrix out) ∧
      (∀ s, s<4 → ∀ l, l<29 → canonical (out s l)) ∧
      (∀ l : Fin 29, coefficients51.eval (ProverCommitQArray48.array 1024#usize (c l.val))=
        ok (ProverCommitQArray48.array 1024#usize (coefficient c hc l.val))) ∧
      ∀ (s : Fin 4) (l : Fin 29), value (out s.val l.val)=
        PhaseLeafEncodingBin.initialSymbol (wideTrace c l) u s := by
  obtain ⟨out,hout,hcout,hdout⟩ := ProverCommitOpenedValues54.exact_result (wide c hc) (wide_canonical c hc) j u hj
  refine ⟨out,hout,hcout,(fun l => (column_spec c hc l).1),?_⟩
  intro s l
  rw [hdout s l]
  unfold symbol PhaseLeafEncodingBin.initialSymbol
  have he : (fun i : Fin 1024 => value (wide c hc l.val i.val))=
      PhaseLeafEncodingBin.coefficients (wideTrace c l) := by
    funext i
    exact wide_value c hc l i
  rw [he]

#print axioms exact_result
end R1Z.ProverCommitOpenedModel54
