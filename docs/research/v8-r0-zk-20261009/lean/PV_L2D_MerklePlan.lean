import Mathlib.Tactic
set_option autoImplicit false
namespace PV_L2D_MerklePlan

abbrev Address := Nat × Nat
abbrev Digest := Fin 32 → UInt8

def sibling (x : Nat) : Nat := 2*(x/2)+(1-x%2)

/-- Binary groups in source order. Fuel is the length of the original index
list; a pair consumes two indices and a singleton consumes one. -/
def level : Nat → List Nat → List Nat × List Nat
  | 0, _ => ([],[])
  | _+1, [] => ([],[])
  | n+1, x::xs =>
    if xs.head? = some (2*(x/2)+1) ∧ x%2=0 then
      let r := level n xs.tail
      (x/2 :: r.1,r.2)
    else
      let r := level n xs
      (x/2 :: r.1,sibling x :: r.2)

/-- Every address is determined from the ordered query indices, including
repeated shared-parent decisions at all eighteen levels. -/
def plan : Nat → Nat → List Nat → List Address
  | 0, _, _ => []
  | n+1, depth, indices =>
    let r := level indices.length indices
    r.2.map (fun child => (depth,child)) ++ plan n (depth+1) r.1

/-- Payload reads are never tested. A digest is exactly 32 bytes. This is the
owned read-plan interface, not yet the native generator refinement. -/
def emit (read : Address → Digest) (addresses : List Address) :
    List UInt8 × List Address :=
  ((addresses.map (fun a => List.ofFn (read a))).flatten,addresses)

theorem erase_payload (r s : Address → Digest) (addresses : List Address) :
    (emit r addresses).2 = (emit s addresses).2 := rfl
#print axioms erase_payload

theorem emitted_length (r : Address → Digest) (addresses : List Address) :
    (emit r addresses).1.length = 32*addresses.length := by
  induction addresses with
  | nil => rfl
  | cons a as ih => simp [emit] at *; omega
#print axioms emitted_length

theorem complete_read_law (r : Address → Digest) (addresses : List Address) :
    emit r addresses = ((addresses.map (fun a => List.ofFn (r a))).flatten,addresses) := rfl
#print axioms complete_read_law

theorem sibling_bound (x n : Nat) (hx : x < 2*n) : sibling x < 2*n := by
  unfold sibling
  omega
#print axioms sibling_bound

theorem parent_bound (x n : Nat) (hx : x < 2*n) : x/2 < n := by omega
#print axioms parent_bound

theorem level_parent_count (fuel : Nat) (indices : List Nat) :
    (level fuel indices).1.length ≤ indices.length := by
  induction fuel generalizing indices with
  | zero => simp [level]
  | succ n ih =>
    cases indices with
    | nil => simp [level]
    | cons x xs =>
      simp only [level]
      split
      · have h := ih xs.tail
        simp only [List.length_cons]
        have ht : xs.tail.length ≤ xs.length := by simp only [List.length_tail]; omega
        omega
      · have h := ih xs
        simp only [List.length_cons]
        omega
#print axioms level_parent_count

theorem level_sibling_count (fuel : Nat) (indices : List Nat) :
    (level fuel indices).2.length ≤ indices.length := by
  induction fuel generalizing indices with
  | zero => simp [level]
  | succ n ih =>
    cases indices with
    | nil => simp [level]
    | cons x xs =>
      simp only [level]
      split
      · have h := ih xs.tail
        have ht : xs.tail.length ≤ xs.length := by simp only [List.length_tail]; omega
        simp only [List.length_cons]
        omega
      · have h := ih xs
        simp only [List.length_cons]
        omega
#print axioms level_sibling_count

theorem plan_bound (levels depth : Nat) (indices : List Nat) :
    (plan levels depth indices).length ≤ levels*indices.length := by
  induction levels generalizing depth indices with
  | zero => simp [plan]
  | succ n ih =>
    simp only [plan,List.length_append,List.length_map]
    have a := level_parent_count indices.length indices
    have b := level_sibling_count indices.length indices
    have c := ih (depth+1) (level indices.length indices).1
    nlinarith
#print axioms plan_bound

theorem binary_native_slot_bound (depth : Nat) (indices : List Nat) (h : indices.length ≤ 16) :
    (emit (fun _ _ => 0) (plan 18 depth indices)).1.length ≤ 32*288 := by
  rw [emitted_length]
  have hp := plan_bound 18 depth indices
  omega
#print axioms binary_native_slot_bound

/-- A small control that preserves sharing, rather than allocating one
independent authentication path per leaf. -/
theorem shared_pair :
    level 2 [0,1] = ([0],[]) ∧ level 2 [0,2] = ([0,1],[1,3]) := by decide
#print axioms shared_pair
end PV_L2D_MerklePlan
