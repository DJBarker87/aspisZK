import R1Z.SideChannelEntropy

/-! A checked obstruction to using arbitrary successful-seed relabelings
as a byte-comparison-preserving coupling. This is NOT a valid-spend attack:
it refutes an intermediate inference, without changing the observer. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_L2_F3SeedObstruction
open R0Z.FsStatement R1Z.ProverCommitPublicNonce40 R1Z.SideChannelEntropy
attribute [local instance] Classical.propDecidable

def seed (position : Fin 32) : OracleAnswer := fun i => if i = position then 1 else 0

def raw (position : Fin 32) : Raw := fun _ => seed position

theorem raw_good (position : Fin 32) : ∀ i, raw position i ≠ 0 := by
  intro i he
  have hh := congrFun he position
  change (if position = position then (1 : UInt8) else 0) = 0 at hh
  simp only [ite_true] at hh
  contradiction

def secretPair (position : Fin 32) : Private := ⟨raw position, raw_good position⟩
def swapSeeds : Private ≃ Private := Equiv.swap (secretPair 0) (secretPair 1)

def firstNonzero (b : OracleAnswer) : Nat :=
  ((List.ofFn b).takeWhile (fun v => v == 0)).length

theorem first_zero : firstNonzero (seed 0) = 0 := by decide

theorem first_one : firstNonzero (seed 1) = 1 := by decide

theorem lifted_position_changes :
    firstNonzero ((lift swapSeeds (raw 0)) 0) ≠ firstNonzero (raw 0 0) := by
  have hl : lift swapSeeds (raw 0) = raw 1 := by
    simp only [lift, decode_success (secretPair 0), swapSeeds, Equiv.swap_apply_left]
    rfl
  rw [hl]
  change firstNonzero (seed 1) ≠ firstNonzero (seed 0)
  rw [first_zero, first_one]
  decide

/-- The very same seed transformation preserves the entire existing L1
entropy state, for all public nonces and byte-blind fault schedules. -/
theorem old_l1_still_equal (nonce : ProverCommitLedger36.Path)
    (schedule : ProverCommitLedger36.Schedule) (tape : Nat → Raw)
    (s : ProverCommitLedger36.State) :
    (generate nonce schedule (fun n => lift swapSeeds (tape n)) s).2 =
      (generate nonce schedule tape s).2 :=
  count_history_preserved swapSeeds nonce schedule tape s

#print axioms raw_good
#print axioms first_zero
#print axioms first_one
#print axioms lifted_position_changes
#print axioms old_l1_still_equal
end R1Z.PV_L2_F3SeedObstruction
