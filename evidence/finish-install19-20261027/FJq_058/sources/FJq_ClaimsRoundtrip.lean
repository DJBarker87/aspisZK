import ClaimsUnrolledFinish
set_option autoImplicit false
namespace AspisR1.FJq_ClaimsRoundtrip
open Aeneas Aeneas.Std ClaimsUnrolledFinish
theorem row {n : Usize} (a : Array MainQM n) : toMainArray (fromMainArray a)=a := by
  apply Subtype.ext
  simp only [toMainArray,fromMainArray,List.map_map]
  have same : toMainQM ∘ fromMainQM=id := by funext x;rfl
  rw [same,List.map_id]
#print axioms row
end AspisR1.FJq_ClaimsRoundtrip
