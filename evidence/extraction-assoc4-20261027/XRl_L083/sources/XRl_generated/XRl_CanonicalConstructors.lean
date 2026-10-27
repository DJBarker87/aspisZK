import XRl_WideCanonical
open Aeneas Aeneas.Std Result
open XRk_Release XRk_FieldExternal XRk_ResultTools
namespace XRl_CanonicalConstructors
#print UScalar.rem_spec
/-- Each successful native-library remainder is below P, including arbitrary
raw 32-bit representatives supplied to the validating constructor. -/
theorem remainder (x y : U32) (run : x % 2147483647#u32=ok y) : y<2147483647#u32 := by
  obtain ⟨z,hz,hval⟩ := WP.spec_imp_exists
    (UScalar.rem_spec (x:=x) (y:=2147483647#u32) (by scalar_tac))
  have same := Result.ok.inj (hz.symm.trans run)
  subst z
  change y.val<(2147483647#u32).val
  rw [hval]
  exact Nat.mod_lt _ (by scalar_tac)
#print axioms remainder
end XRl_CanonicalConstructors
