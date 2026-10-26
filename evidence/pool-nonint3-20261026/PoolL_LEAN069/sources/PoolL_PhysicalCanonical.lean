import PoolL_Physical
set_option autoImplicit false
namespace AspisR1.PoolL_PhysicalCanonical
open Aeneas Aeneas.Std Result PoolL_Physical

theorem excluded (s : Snapshot) (key id : Key) (cp : Occupied s key) :
    PoolL_CanonicalRoleSource.PoolL_canonical_role (observe s key) id (.Ok (bytes s key)) ≠
      ok (.Ok ()) := PoolL_CanonicalRoleReject.occupied _ _ _ cp
#print axioms excluded
end AspisR1.PoolL_PhysicalCanonical
