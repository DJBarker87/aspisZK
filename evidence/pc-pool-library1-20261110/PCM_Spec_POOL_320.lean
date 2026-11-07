import RSL_Pool
set_option autoImplicit false
namespace PCM_POOL_320
open RSL
/-- The copied afterstate fields read by frozen pair_forest.rs:1388-1407.
Extent is an input representation clause, not a success hypothesis. -/
structure Afterstate where
  next_pair_index : UInt64
  next_root : Digest
  next_frontier : List Digest

def Domain (lane : LaneState) (a : Afterstate) : Prop :=
  lane.tree.frontier.length = TREE_DEPTH ∧ a.next_frontier.length = TREE_DEPTH

/-- Checked u64 increment and the ordered frontier guard. The predicate is
pure: the loop has no visible effects and its first error is always 0x41532003. -/
def Ref (lane : LaneState) (a : Afterstate) : Except ProgramError LaneState :=
  if lane.tree.next_leaf_index == 0xffffffffffffffff ||
      lane.tree.next_leaf_index + 1 != a.next_pair_index then
    .error (.custom 0x41532003)
  else if (a.next_frontier.zipIdx).any (fun (node, level) =>
      ((a.next_pair_index >>> level.toUInt64) &&& 1) == 0 &&
        decide (node ≠ EMPTY_ROOTS[level]!)) then
    .error (.custom 0x41532003)
  else .ok { lane with tree := ⟨a.next_pair_index, a.next_root, a.next_frontier⟩ }

def RowSpec (impl : LaneState → Afterstate → Env → Obs (Except ProgramError LaneState)) : Prop :=
  ∀ lane a, Domain lane a → ∀ env, impl lane a env = ⟨.ret (Ref lane a), []⟩

/-- An implementation returning a different error is rejected on a concrete
well-shaped input; no assumption about a child reply enters this witness. -/
theorem rejects_wrong_error :
    ¬ RowSpec (fun _ _ _ => ⟨.ret (.error .invalidArgument), []⟩) := by
  intro h
  let lane : LaneState := ⟨0, zero32, 0, ⟨0xffffffffffffffff, [], List.replicate 20 []⟩⟩
  let a : Afterstate := ⟨0, [], List.replicate 20 []⟩
  have hd : Domain lane a := by constructor <;> rfl
  have he := h lane a hd env0
  have hh : Ref lane a = .error (.custom 0x41532003) := by rfl
  rw [hh] at he
  cases he

#print axioms rejects_wrong_error
end PCM_POOL_320
