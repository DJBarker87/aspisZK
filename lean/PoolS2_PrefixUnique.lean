import PoolS2_Prefix
set_option autoImplicit false
namespace AspisR1.PoolS2_PrefixUnique
open Aeneas Aeneas.Std Result PoolS2_Prefix PoolS2_PrefixSource

theorem accepted (accounts : Slice Account) :
    unique accounts = ok (.Ok ()) ↔ PoolS2_UniqueSuffix.allDifferent (keys accounts).val := by
  classical
  rw [unique,PoolS2_UniqueExact.exact]
  by_cases distinct : PoolS2_UniqueSuffix.allDifferent (keys accounts).val <;> simp [distinct]

theorem keys_count (accounts : Slice Account) :
    (keys accounts).val.length = accounts.val.length := by simp [keys]

#print axioms accepted
#print axioms keys_count
end AspisR1.PoolS2_PrefixUnique
