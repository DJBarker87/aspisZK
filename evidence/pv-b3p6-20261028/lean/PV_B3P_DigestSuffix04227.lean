import PV_B3P_DigestStage04227
import PV_B3P_DigestBranch227
import PV_B3P_DigestSuffix05227
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false
def digest_suffix_04 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) : Result Digest8Q := do
  let block ← lift (Std.Usize.wrapping_add 34#usize 0#usize)
  let i6 ←
    lift (Std.U64.wrapping_shr public1.transition.live_snapshot.next_pair_index
      0#u32)
  let i7 ← lift (i6 &&& 1#u64)
  let digests5 ←
    if i7 = 0#u64
    then
      do
      let i8 ← lift (Std.Usize.wrapping_mul block 16#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i8
      let a ← reference_terminal.empty_root 0#usize
      reference_terminal.add_digest_binding output q3 openings.z
        aspis_statement.poseidon2.RATE a true
    else
      do
      let i8 ← lift (Std.Usize.wrapping_mul block 16#usize)
      let i9 ← lift (Std.Usize.wrapping_add i8 12#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i9
      let a ←
        reference_terminal.digest227 public1.transition.live_snapshot.frontier
          0#usize
      reference_terminal.add_digest_binding output q3 openings.z 0#usize a
        false
  digest_suffix_05 public1 openings selectors digests5

attribute [local irreducible] reference_terminal.add_digest_binding reference_copy_terminal.Selectors.row reference_terminal.empty_root reference_terminal.digest227 reference_terminal.bounded_append_carry digest_suffix_05

theorem digest_suffix_04_equation (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_suffix_04 public1 openings selectors output = digest_stage_04 public1 openings selectors output >>= digest_suffix_05 public1 openings selectors := by
  simp only [digest_suffix_04,digest_stage_04,digest_assoc,digest_if_bind,digest_option_bind]

theorem digest_suffix_04_success (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    Success (digest_suffix_04 public1 openings selectors output) := by
  rw [digest_suffix_04_equation]
  apply bind
  · exact digest_stage_04_success public1 openings selectors output
  intro next
  exact digest_suffix_05_success public1 openings selectors next

#print axioms digest_suffix_04_equation
#print axioms digest_suffix_04_success
end PV_B3P_Success227
