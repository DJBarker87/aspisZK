import NLU_State
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLU_Generated
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open RawExtractedSemanticCallOpsV20
open ExtractedMaskQM31Exact (CurrentCanonicalQM decode)
/-- Direct paired law for the ACTUAL emitted multiplication definition.
Generated/probe equality plus the already proved canonical value theorem;
no multiplication proof or evaluator is run in Kani. -/
theorem emitted_mul (x y : GenQ) (hx : CurrentCanonicalQM (genQToProbe x))
 (hy : CurrentCanonicalQM (genQToProbe y)) :
 ∃ z,AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul x y=ok z ∧
 CurrentCanonicalQM (genQToProbe z) ∧
 decode (genQToProbe z)=decode (genQToProbe x)*decode (genQToProbe y) := by
 obtain ⟨p,probe,canonical,value⟩:=ExtractedMaskQM31Exact.current_qm_mul_exact
  (genQToProbe x) (genQToProbe y) hx hy
 have same:=generated_qm_mul_eq_probe x y
 rw [probe] at same
 cases run : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul x y with
 | fail err=>rw [run] at same;cases same
 | div=>rw [run] at same;cases same
 | ok z=>
   rw [run] at same
   change ok (genQToProbe z)=ok p at same
   have selected:=Result.ok.inj same
   refine ⟨z,rfl,?_,?_⟩
   · rw [selected];exact canonical
   · rw [selected];exact value
#print axioms emitted_mul
set_option pp.proofs false in #print emitted_mul
end AspisR1.NLU_Generated
end
