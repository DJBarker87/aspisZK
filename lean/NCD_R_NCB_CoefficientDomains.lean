-- Retargeted inherited proof body; only module imports changed.
import NCD_R_NBS_PowersCanon
set_option autoImplicit false
namespace NCB_CoefficientDomains
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues
/-- The SAME returned powers carrier is canonical. Determinism identifies it
with the existing constructed source result, rather than choosing another g. -/
theorem returned (gamma : NE) (canonical : canonE gamma)
    (g : Array NE 29#usize)
    (run : FIo_Native.weights.powers 29#usize gamma=ok g) : FIo_ArrayCanon.Holds g := by
  obtain ⟨selected,source,domain⟩ := NBS_PowersCanon.source gamma canonical
  have same : selected=g := Result.ok.inj (source.symm.trans run)
  exact same ▸ domain
#print axioms returned
end NCB_CoefficientDomains
