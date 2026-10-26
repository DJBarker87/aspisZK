import PoolL_Physical
set_option autoImplicit false
namespace AspisR1.PoolL_PhysicalMarker
open Aeneas Aeneas.Std Result PoolL_Physical

theorem excluded (s : Snapshot) (key id system : Key) (cp : Occupied s key) :
    PoolL_MarkerRoleSource.PoolL_marker_role (observe s key) id system
      (decide ((bytes s key).val.length = 0)) (.Ok (bytes s key)) =
      ok (.Err (.Custom 1095966757#u32)) := by
  have nz : (bytes s key).val.length ≠ 0 := by rcases cp with h | h <;> omega
  simp only [nz,decide_false]
  exact PoolL_MarkerRoleReject.occupied _ _ _ _ cp
#print axioms excluded
end AspisR1.PoolL_PhysicalMarker
