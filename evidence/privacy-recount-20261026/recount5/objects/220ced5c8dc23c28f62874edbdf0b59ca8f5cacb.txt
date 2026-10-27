import R1Z.PV_Canon_Result
import R1Z.ProverCommitArrayIndex25
set_option autoImplicit false
namespace R1Z.PV_Canon
open Aeneas Aeneas.Std Result ProverRwFull
 theorem coefficient_read (p : Array aspis_core.field.QM31 28#usize) (hp : Coeffs p)
    (i : Usize) (hi : i.val < 28) : Safe Q (Array.index_usize p i) := by
  have bound : i.val < p.val.length := by rw [p.property]; exact hi
  apply safe_of_total
  refine ⟨p.val[i.val],ProverCommitArrayIndex25.array_index_usize_ok p i hi,?_⟩
  exact hp _ (List.getElem_mem bound)
#print axioms coefficient_read
end R1Z.PV_Canon
