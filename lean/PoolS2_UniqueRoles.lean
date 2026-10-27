import PoolS2_UniqueExact
set_option autoImplicit false
namespace AspisR1.PoolS2_UniqueRoles
open Aeneas Aeneas.Std Result PoolS2_RightStep PoolS2_UniqueSuffix

theorem ordered (keys : List Key) (unique : allDifferent keys) (i j : Nat)
    (hi : i < keys.length) (hj : j < keys.length) (before : i < j) :
    (keys[i]).val ≠ (keys[j]).val := by
  induction keys generalizing i j with
  | nil => simp at hi
  | cons key rest ih =>
    obtain ⟨head,tail⟩ := List.pairwise_cons.mp unique
    cases i with
    | zero =>
      cases j with
      | zero => omega
      | succ j =>
        exact head (rest[j]'(by simpa using hj)) (List.getElem_mem (by simpa using hj))
    | succ i =>
      cases j with
      | zero => omega
      | succ j =>
        exact ih tail i j (by simpa using hi) (by simpa using hj) (by omega)

theorem checkpoint_master (keys : Slice Key) (count : keys.val.length = 12)
    (accepted : PoolS2_Unique.unique_keys keys = ok true) :
    (keys.val[9]'(by omega)).val ≠ (keys.val[0]'(by omega)).val := by
  have unique := PoolS2_UniqueExact.accepted keys |>.mp accepted
  exact (ordered keys.val unique 0 9 (by omega) (by omega) (by omega)).symm

#print axioms ordered
#print axioms checkpoint_master
end AspisR1.PoolS2_UniqueRoles
