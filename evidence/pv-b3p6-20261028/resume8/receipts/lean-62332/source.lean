import PV_B3P_DigestStage16227
import PV_B3P_DigestBranch227
import PV_B3P_DigestSuffix17227
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false
def digest_suffix_16 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) : Result Digest8Q := do
  let block12 ← lift (Std.Usize.wrapping_add 34#usize 12#usize)
  let i30 ←
    lift (Std.U64.wrapping_shr public1.transition.live_snapshot.next_pair_index
      12#u32)
  let i31 ← lift (i30 &&& 1#u64)
  let digests17 ←
    if i31 = 0#u64
    then
      do
      let i32 ← lift (Std.Usize.wrapping_mul block12 16#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i32
      let a ← reference_terminal.empty_root 12#usize
      reference_terminal.add_digest_binding output q3 openings.z
        aspis_statement.poseidon2.RATE a true
    else
      do
      let i32 ← lift (Std.Usize.wrapping_mul block12 16#usize)
      let i33 ← lift (Std.Usize.wrapping_add i32 12#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i33
      let a ←
        reference_terminal.digest227 public1.transition.live_snapshot.frontier
          12#usize
      reference_terminal.add_digest_binding output q3 openings.z 0#usize a
        false
  digest_suffix_17 public1 openings selectors digests17

attribute [local irreducible] reference_terminal.add_digest_binding reference_copy_terminal.Selectors.row reference_terminal.empty_root reference_terminal.digest227 reference_terminal.bounded_append_carry digest_suffix_17

theorem digest_suffix_16_equation (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_suffix_16 public1 openings selectors output = digest_stage_16 public1 openings selectors output >>= digest_suffix_17 public1 openings selectors := by
  simp only [digest_suffix_16,digest_stage_16,digest_assoc,digest_if_bind,digest_option_bind]

theorem digest_suffix_16_success (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    Success (digest_suffix_16 public1 openings selectors output) := by
  rw [digest_suffix_16_equation]
  apply bind
  · exact digest_stage_16_success public1 openings selectors output
  intro next
  exact digest_suffix_17_success public1 openings selectors next

#print axioms digest_suffix_16_equation
#print axioms digest_suffix_16_success
end PV_B3P_Success227
