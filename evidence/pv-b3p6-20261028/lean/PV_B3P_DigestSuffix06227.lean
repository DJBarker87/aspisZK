import PV_B3P_DigestStage06227
import PV_B3P_DigestAssoc227
import PV_B3P_DigestSuffix07227
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false
def digest_suffix_06 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) : Result Digest8Q := do
  let block2 ← lift (Std.Usize.wrapping_add 34#usize 2#usize)
  let i10 ←
    lift (Std.U64.wrapping_shr public1.transition.live_snapshot.next_pair_index
      2#u32)
  let i11 ← lift (i10 &&& 1#u64)
  let digests7 ←
    if i11 = 0#u64
    then
      do
      let i12 ← lift (Std.Usize.wrapping_mul block2 16#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i12
      let a ← reference_terminal.empty_root 2#usize
      reference_terminal.add_digest_binding output q3 openings.z
        aspis_statement.poseidon2.RATE a true
    else
      do
      let i12 ← lift (Std.Usize.wrapping_mul block2 16#usize)
      let i13 ← lift (Std.Usize.wrapping_add i12 12#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i13
      let a ←
        reference_terminal.digest227 public1.transition.live_snapshot.frontier
          2#usize
      reference_terminal.add_digest_binding output q3 openings.z 0#usize a
        false
  digest_suffix_07 public1 openings selectors digests7

attribute [local irreducible] reference_terminal.add_digest_binding reference_copy_terminal.Selectors.row reference_terminal.empty_root reference_terminal.digest227 reference_terminal.bounded_append_carry digest_suffix_07

theorem digest_suffix_06_equation (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_suffix_06 public1 openings selectors output = digest_stage_06 public1 openings selectors output >>= digest_suffix_07 public1 openings selectors := by
  simp only [digest_suffix_06,digest_stage_06,digest_assoc]

theorem digest_suffix_06_success (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    Success (digest_suffix_06 public1 openings selectors output) := by
  rw [digest_suffix_06_equation]
  apply bind
  · exact digest_stage_06_success public1 openings selectors output
  intro next
  exact digest_suffix_07_success public1 openings selectors next

#print axioms digest_suffix_06_equation
#print axioms digest_suffix_06_success
end PV_B3P_Success227
