import NCV_DigestEquality
import NCV_Reference.Funs
set_option autoImplicit false
namespace NDB_PrimaryEquality
open Aeneas Aeneas.Std Result
/-- The primary and checked-cast references share the exact digest equality loop. -/
theorem digest_equal (a b : Array U32 8#usize) :
    NCV_Reference.eq_digest a b = NCV_CastRef.eq_digest a b := by rfl

theorem digest_reflexive (a : Array U32 8#usize) :
    NCV_Reference.eq_digest a a = ok true := by
  rw [digest_equal]
  exact NCV_DigestEquality.reflexive a
#print axioms digest_equal
#print axioms digest_reflexive
end NDB_PrimaryEquality
