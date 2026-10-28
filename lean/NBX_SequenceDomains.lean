import NBX_RowFrames
set_option autoImplicit false
namespace NBX_SequenceDomains
/-- Native offsets of one u64 row; every read is exactly eight bytes. -/
def start (base lane : Nat) : Nat := base + 8*lane

theorem within (base count lane length : Nat) (index : lane < count)
    (fit : base + 8*count ≤ length) : start base lane + 8 ≤ length := by
  unfold start
  omega

theorem disjoint (base i j : Nat) (ordered : i < j) :
    start base i + 8 ≤ start base j := by
  unfold start
  omega

theorem master (lane : Nat) (index : lane < 8) :
    320 ≤ start 320 lane ∧ start 320 lane + 8 ≤ 384 := by
  unfold start
  omega

theorem checkpoint (lane : Nat) (index : lane < 8) :
    112 ≤ start 112 lane ∧ start 112 lane + 8 ≤ 176 := by
  unfold start
  omega

/-- Checkpoint sequence reads fit the guarded192-byte input and precede its
reserved suffix. The native iterator/caller association remains separate. -/
theorem checkpoint_input (lane : Nat) (index : lane < 8) :
    start 112 lane + 8 ≤ 192 := by
  have := (checkpoint lane index).2
  omega

#print axioms within
#print axioms disjoint
#print axioms master
#print axioms checkpoint
#print axioms checkpoint_input
end NBX_SequenceDomains
