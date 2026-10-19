import ActualMainMaskPopulatedBridge
import ActualMainMaskSemanticBridge

/-! Both checked meanings concern the same deterministic extracted mask
call. Its unique successful output identifies the mapped populated polynomial
with the existing R0P mask value, without reevaluating coefficients or powers. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.ActualMainMaskR0PValue
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.RawSemanticFieldOwnerAdapter
open AspisR1PublicPreparation.ActualMainMaskPopulatedBridge
abbrev W := AspisWideTower.WideExact

 theorem mapped_populated_mask_eq_R0P
    (c1 : Array MainQM 16#usize) (maskOnly : Array MainQM 10#usize)
    (g : MainQM) (point : Array MainQM 10#usize)
    (hc1 : CanonicalArray c1) (hmask : CanonicalArray maskOnly)
    (hg : Canonical (mainToProbe g)) (hpoint : CanonicalArray point) :
    algebraMap E W (maskValue c1 maskOnly g point) =
      ActualMainMaskSemanticBridge.maskValue c1 maskOnly g point := by
  obtain ⟨out,hrun,hcanonical,hvalue⟩ :=
    extractedMainMask_refines c1 maskOnly g point hc1 hmask hg hpoint
  obtain ⟨outWide,hrunWide,hcanonicalWide,hvalueWide⟩ :=
    ActualMainMaskSemanticBridge.extractedMainMask_refines
      c1 maskOnly g point hc1 hmask hg hpoint
  have hout : outWide = out := Result.ok.inj (hrunWide.symm.trans hrun)
  subst outWide
  have hwide : algebraMap E W (fieldValue out) =
      ActualMainMaskSemanticBridge.maskValue c1 maskOnly g point := by
    simpa only [fieldValue, ActualMainMaskSemanticBridge.fieldValue] using hvalueWide
  exact (congrArg (algebraMap E W) hvalue).symm.trans hwide

#print axioms mapped_populated_mask_eq_R0P
end AspisR1PublicPreparation.ActualMainMaskR0PValue
end
