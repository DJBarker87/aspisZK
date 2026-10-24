import S1ValuesOwnedInstallationV1
import S1ValuesOwnedTotalV1
set_option autoImplicit false
namespace AspisS1ValuesOwnedInstallation
open Aeneas Aeneas.Std Result

/-- TOTAL installed value leaf for every full input/output buffer whose input
length can be doubled. Includes Rust codec rejection, not only Ok(()). -/
theorem expandValues_total (input output : Slice U8)
    (doubling : 2*input.length ≤ Usize.max) :
    ∃ status updated, expandValues input output=ok (status,updated) := by
  obtain ⟨result,call⟩ := AspisS1ValuesOwnedTotal.reference_total (toVec input) (toVec output) doubling
  rcases result with ⟨status,next,updated⟩
  refine ⟨status,toSlice updated,?_⟩
  simp only [expandValues,call,bind_tc_ok]
  rfl

#print axioms expandValues_total
end AspisS1ValuesOwnedInstallation
