import PV_B3P_DigestStage12227
import PV_B3P_DigestBranch227
import PV_B3P_DigestSuffix13227
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false
def digest_suffix_12 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) : Result Digest8Q := do
  let block8 ← lift (Std.Usize.wrapping_add 34#usize 8#usize)
  let i22 ←
    lift (Std.U64.wrapping_shr public1.transition.live_snapshot.next_pair_index
      8#u32)
  let i23 ← lift (i22 &&& 1#u64)
  let digests13 ←
    if i23 = 0#u64
    then
      do
      let i24 ← lift (Std.Usize.wrapping_mul block8 16#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i24
      let a ← reference_terminal.empty_root 8#usize
      reference_terminal.add_digest_binding output q3 openings.z
        aspis_statement.poseidon2.RATE a true
    else
      do
      let i24 ← lift (Std.Usize.wrapping_mul block8 16#usize)
      let i25 ← lift (Std.Usize.wrapping_add i24 12#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i25
      let a ←
        reference_terminal.digest227 public1.transition.live_snapshot.frontier
          8#usize
      reference_terminal.add_digest_binding output q3 openings.z 0#usize a
        false
  digest_suffix_13 public1 openings selectors digests13

attribute [local irreducible] reference_terminal.add_digest_binding reference_copy_terminal.Selectors.row reference_terminal.empty_root reference_terminal.digest227 reference_terminal.bounded_append_carry digest_suffix_13

theorem digest_suffix_12_equation (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_suffix_12 public1 openings selectors output = digest_stage_12 public1 openings selectors output >>= digest_suffix_13 public1 openings selectors := by
  simp only [digest_suffix_12,digest_stage_12,digest_assoc,digest_if_bind,digest_option_bind]

theorem digest_suffix_12_success (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    Success (digest_suffix_12 public1 openings selectors output) := by
  rw [digest_suffix_12_equation]
  apply bind
  · exact digest_stage_12_success public1 openings selectors output
  intro next
  exact digest_suffix_13_success public1 openings selectors next

#print axioms digest_suffix_12_equation
#print axioms digest_suffix_12_success
end PV_B3P_Success227
