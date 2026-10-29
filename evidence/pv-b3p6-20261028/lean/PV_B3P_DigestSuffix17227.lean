import PV_B3P_DigestStage17227
import PV_B3P_DigestBranch227
import PV_B3P_DigestSuffix18227
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false
def digest_suffix_17 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) : Result Digest8Q := do
  let block13 ← lift (Std.Usize.wrapping_add 34#usize 13#usize)
  let i32 ←
    lift (Std.U64.wrapping_shr public1.transition.live_snapshot.next_pair_index
      13#u32)
  let i33 ← lift (i32 &&& 1#u64)
  let digests18 ←
    if i33 = 0#u64
    then
      do
      let i34 ← lift (Std.Usize.wrapping_mul block13 16#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i34
      let a ← reference_terminal.empty_root 13#usize
      reference_terminal.add_digest_binding output q3 openings.z
        aspis_statement.poseidon2.RATE a true
    else
      do
      let i34 ← lift (Std.Usize.wrapping_mul block13 16#usize)
      let i35 ← lift (Std.Usize.wrapping_add i34 12#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i35
      let a ←
        reference_terminal.digest227 public1.transition.live_snapshot.frontier
          13#usize
      reference_terminal.add_digest_binding output q3 openings.z 0#usize a
        false
  digest_suffix_18 public1 openings selectors digests18

attribute [local irreducible] reference_terminal.add_digest_binding reference_copy_terminal.Selectors.row reference_terminal.empty_root reference_terminal.digest227 reference_terminal.bounded_append_carry digest_suffix_18

theorem digest_suffix_17_equation (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_suffix_17 public1 openings selectors output = digest_stage_17 public1 openings selectors output >>= digest_suffix_18 public1 openings selectors := by
  simp only [digest_suffix_17,digest_stage_17,digest_assoc,digest_if_bind,digest_option_bind]

theorem digest_suffix_17_success (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    Success (digest_suffix_17 public1 openings selectors output) := by
  rw [digest_suffix_17_equation]
  apply bind
  · exact digest_stage_17_success public1 openings selectors output
  intro next
  exact digest_suffix_18_success public1 openings selectors next

#print axioms digest_suffix_17_equation
#print axioms digest_suffix_17_success
end PV_B3P_Success227
