import PV_B3P_DigestStage15227
import PV_B3P_DigestBranch227
import PV_B3P_DigestSuffix16227
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false
def digest_suffix_15 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) : Result Digest8Q := do
  let block11 ← lift (Std.Usize.wrapping_add 34#usize 11#usize)
  let i28 ←
    lift (Std.U64.wrapping_shr public1.transition.live_snapshot.next_pair_index
      11#u32)
  let i29 ← lift (i28 &&& 1#u64)
  let digests16 ←
    if i29 = 0#u64
    then
      do
      let i30 ← lift (Std.Usize.wrapping_mul block11 16#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i30
      let a ← reference_terminal.empty_root 11#usize
      reference_terminal.add_digest_binding output q3 openings.z
        aspis_statement.poseidon2.RATE a true
    else
      do
      let i30 ← lift (Std.Usize.wrapping_mul block11 16#usize)
      let i31 ← lift (Std.Usize.wrapping_add i30 12#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i31
      let a ←
        reference_terminal.digest227 public1.transition.live_snapshot.frontier
          11#usize
      reference_terminal.add_digest_binding output q3 openings.z 0#usize a
        false
  digest_suffix_16 public1 openings selectors digests16

attribute [local irreducible] reference_terminal.add_digest_binding reference_copy_terminal.Selectors.row reference_terminal.empty_root reference_terminal.digest227 reference_terminal.bounded_append_carry digest_suffix_16

theorem digest_suffix_15_equation (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_suffix_15 public1 openings selectors output = digest_stage_15 public1 openings selectors output >>= digest_suffix_16 public1 openings selectors := by
  simp only [digest_suffix_15,digest_stage_15,digest_assoc,digest_if_bind,digest_option_bind]

theorem digest_suffix_15_success (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    Success (digest_suffix_15 public1 openings selectors output) := by
  rw [digest_suffix_15_equation]
  apply bind
  · exact digest_stage_15_success public1 openings selectors output
  intro next
  exact digest_suffix_16_success public1 openings selectors next

#print axioms digest_suffix_15_equation
#print axioms digest_suffix_15_success
end PV_B3P_Success227
