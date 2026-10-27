import R1Z.ProverCommitMultiproof46

/-! Source-linked structural multiproof reference, using the existing checked
binary group/cursor. This is not a theorem about native sort/Vec/BTree costs. -/
set_option autoImplicit false
namespace R1Z.PV_L2_F6Sharing
open Aeneas Aeneas.Std R1Z.ProverCommitBinaryGroup46
  R1Z.ProverCommitBinarySupport46

/-- Complete ordered group decisions for one source-linked binary layer. -/
def groups : List U32 → List (U32 × Option U32 × Usize × Option U32)
  | [] => []
  | a :: tail =>
    let g := group a tail.head?
    (a,tail.head?,g.consumed,g.sibling) :: groups (tail.drop (g.consumed.val-1))
termination_by xs => xs.length
decreasing_by simp only [List.length_cons, List.length_drop]; omega

def structural : Nat → List U32 → List (List U32 × List (U32 × Option U32 × Usize × Option U32) × List U32)
  | 0, _ => []
  | n+1, xs => (xs,groups xs,(layer xs).2) :: structural n (layer xs).1

/-- Carries the exact request count/sequence with the source cursor result. -/
theorem cursor_joint (xs : List U32) :
    (R1Z.ProverCommitBinaryCursor46.source xs.length xs, groups xs) =
      (Result.ok (layer xs),groups xs) := by
  rw [R1Z.ProverCommitBinaryCursor46.native_layer]

theorem singleton_layer (a : U32) :
    layer [a] = ([U32.wrapping_shr a 1#u32],[a ^^^ 1#u32]) := by
  simp only [layer, List.head?_nil, group, reduceCtorEq, if_false,
    List.drop_nil, List.append_nil, Option.toList_some]

theorem singleton_count (n : Nat) (a : U32) : count n [a] = n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    have hc := layer_count [a]
    rw [singleton_layer] at hc
    simp only [count,hc.1,hc.2,List.length_singleton,ih]
    omega

theorem request_depths (n : Nat) (xs : List U32) : (structural n xs).length = n := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih => simp only [structural,List.length_cons,ih]

/-- Arbitrarily different payloads may produce different bytes, while all
structural groups and sibling requests remain the same. No payload equality
or equality of final roots is needed for this local observation. -/
theorem payload_erasure (left right : Nat → U32 → R1Z.ProverCommitPublish43.Bytes)
    (n depth : Nat) (xs : List U32) :
    (structural n xs, levels left n depth xs).1 =
      (structural n xs, levels right n depth xs).1 := rfl

#print axioms cursor_joint
#print axioms singleton_layer
#print axioms singleton_count
#print axioms request_depths
#print axioms payload_erasure
end R1Z.PV_L2_F6Sharing
