import R1Z.PV_CBL_CoreNewOwned
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_CoreNewCases
set_option autoImplicit false
theorem total (n : Usize) : ∃ result, PV_CBL_CoreNewOwned.sha_core_new_owned n=ok result := by
  unfold PV_CBL_CoreNewOwned.sha_core_new_owned
  split <;> exact ⟨_,rfl⟩
theorem unsupported (n : Usize) (h28 : n.val≠28) (h32 : n.val≠32) :
    PV_CBL_CoreNewOwned.sha_core_new_owned n=ok (.Err ()) := by
  simp [PV_CBL_CoreNewOwned.sha_core_new_owned,h28,h32]
theorem no_extraction_failure (n : Usize) (e : Error) :
    PV_CBL_CoreNewOwned.sha_core_new_owned n≠fail e := by
  obtain ⟨r,hr⟩ := total n
  rw [hr]
  intro h
  cases h
#print axioms total
#print axioms unsupported
#print axioms no_extraction_failure
end R1Z.PV_CBL_CoreNewCases
