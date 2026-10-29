import PV_RJ4IDB_OpenInputs
set_option autoImplicit false
namespace PV_L1E_PrefixObstruction
open PV_RJ4IDB

/-- Equality of completed count/rejection lists does not imply equality at the
same earlier position in the ordered world. This is event algebra, not a
counterexample against any honest deployed execution. -/
theorem completed_counts_do_not_determine_prefix :
    ∃ left right : List NativeEvent,
      nativeCounts left = nativeCounts right ∧
      nativeRejections left = nativeRejections right ∧
      nativeCounts (left.take 1) ≠ nativeCounts (right.take 1) := by
  refine ⟨[.count 1,.side [] []],[.side [] [],.count 1],rfl,rfl,?_⟩
  intro impossible
  cases impossible
#print axioms completed_counts_do_not_determine_prefix

/-- The analogous issue for a rejected attempt: preserving only a completed
rejection list cannot certify an interrupted prefix before its occurrence. -/
theorem completed_rejections_do_not_determine_prefix :
    ∃ left right : List NativeEvent,
      nativeCounts left = nativeCounts right ∧
      nativeRejections left = nativeRejections right ∧
      nativeRejections (left.take 1) ≠ nativeRejections (right.take 1) := by
  refine ⟨[.rejection 0,.side [] []],[.side [] [],.rejection 0],rfl,rfl,?_⟩
  intro impossible
  cases impossible
#print axioms completed_rejections_do_not_determine_prefix
end PV_L1E_PrefixObstruction
