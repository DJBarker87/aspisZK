import PV_B3P_DigestRaw8227
import PV_B3P_DigestStage24227
import PV_B3P_DigestBranch227
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false
attribute [local irreducible] reference_terminal.add_digest_binding reference_copy_terminal.Selectors.row reference_terminal.empty_root reference_terminal.digest227 reference_terminal.bounded_append_carry

def digest_head_24 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) : Result Digest8Q := do
  let i46 ← lift (Std.Usize.wrapping_mul 53#usize 16#usize)
  let i47 ← lift (Std.Usize.wrapping_add i46 11#usize)
  let q3 ← reference_copy_terminal.Selectors.row selectors i47
  let digests25 ←
    reference_terminal.add_digest_binding output q3 openings.z 0#usize
      public1.transition.candidate_afterstate.next_root false
  let carry ←
    reference_terminal.bounded_append_carry
      public1.transition.live_snapshot.next_pair_index
  if carry < 20#usize
  then
    let i48 ← lift (Std.Usize.wrapping_add 33#usize carry)
    let i49 ← lift (Std.Usize.wrapping_mul i48 16#usize)
    let i50 ← lift (Std.Usize.wrapping_add i49 11#usize)
    let q4 ← reference_copy_terminal.Selectors.row selectors i50
    let a ←
      Array.index_usize public1.transition.candidate_afterstate.next_frontier
        carry
    reference_terminal.add_digest_binding digests25 q4 openings.z 0#usize a
      false
  else Result.ok digests25

theorem digest_head_24_factor (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_raw_24 public1 openings selectors output = digest_head_24 public1 openings selectors output := by
  rfl

theorem digest_head_24_equation (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_head_24 public1 openings selectors output = digest_stage_24 public1 openings selectors output := by
  simp only [digest_head_24,digest_stage_24,digest_assoc,digest_if_bind,digest_option_bind]

theorem digest_raw_24_success (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    Success (digest_raw_24 public1 openings selectors output) := by
  rw [digest_head_24_factor,digest_head_24_equation]
  exact digest_stage_24_success public1 openings selectors output

#print axioms digest_head_24_factor
#print axioms digest_head_24_equation
#print axioms digest_raw_24_success
end PV_B3P_Success227
