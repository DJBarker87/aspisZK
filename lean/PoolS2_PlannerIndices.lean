import PoolS2_PlannerBindings
set_option autoImplicit false
namespace AspisR1.PoolS2_PlannerIndices
open Aeneas Aeneas.Std Result PoolS2_PdaSource PoolS2_Lanes PoolS2_PlannerModel

theorem accepted (m : Master) (lanes : Lanes) (root : Root) (bump : U8) (p : Plan)
    (h : run m lanes root bump = ok (.Ok p)) (i : Nat) (within : i < 8) :
    p.checkpoint.lane_sequences.val[i]'(by simpa using within) =
      (lanes.val[i]'(by simpa using within)).tree.next_leaf_index := by
  have bound : i < lanes.val.length := by simpa using within
  have image := (PoolS2_PlannerBindings.accepted m lanes root bump p h).2.2.2.2.2.1
  have contents : p.checkpoint.lane_sequences.val = (sequences lanes).val := congrArg Subtype.val image
  simpa [sequences,List.getElem?_eq_getElem,within,bound] using
    congrArg (fun xs : List U64 => xs[i]?) contents

#print axioms accepted
end AspisR1.PoolS2_PlannerIndices
