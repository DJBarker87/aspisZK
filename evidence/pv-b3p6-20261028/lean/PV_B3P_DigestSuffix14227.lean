import PV_B3P_DigestStage14227
import PV_B3P_DigestBranch227
import PV_B3P_DigestSuffix15227
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false
def digest_suffix_14 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) : Result Digest8Q := do
  let block10 ← lift (Std.Usize.wrapping_add 34#usize 10#usize)
  let i26 ←
    lift (Std.U64.wrapping_shr public1.transition.live_snapshot.next_pair_index
      10#u32)
  let i27 ← lift (i26 &&& 1#u64)
  let digests15 ←
    if i27 = 0#u64
    then
      do
      let i28 ← lift (Std.Usize.wrapping_mul block10 16#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i28
      let a ← reference_terminal.empty_root 10#usize
      reference_terminal.add_digest_binding output q3 openings.z
        aspis_statement.poseidon2.RATE a true
    else
      do
      let i28 ← lift (Std.Usize.wrapping_mul block10 16#usize)
      let i29 ← lift (Std.Usize.wrapping_add i28 12#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i29
      let a ←
        reference_terminal.digest227 public1.transition.live_snapshot.frontier
          10#usize
      reference_terminal.add_digest_binding output q3 openings.z 0#usize a
        false
  digest_suffix_15 public1 openings selectors digests15

attribute [local irreducible] reference_terminal.add_digest_binding reference_copy_terminal.Selectors.row reference_terminal.empty_root reference_terminal.digest227 reference_terminal.bounded_append_carry digest_suffix_15

theorem digest_suffix_14_equation (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_suffix_14 public1 openings selectors output = digest_stage_14 public1 openings selectors output >>= digest_suffix_15 public1 openings selectors := by
  simp only [digest_suffix_14,digest_stage_14,digest_assoc,digest_if_bind,digest_option_bind]

theorem digest_suffix_14_success (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    Success (digest_suffix_14 public1 openings selectors output) := by
  rw [digest_suffix_14_equation]
  apply bind
  · exact digest_stage_14_success public1 openings selectors output
  intro next
  exact digest_suffix_15_success public1 openings selectors next

#print axioms digest_suffix_14_equation
#print axioms digest_suffix_14_success
end PV_B3P_Success227
