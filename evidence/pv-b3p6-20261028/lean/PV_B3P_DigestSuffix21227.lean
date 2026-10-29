import PV_B3P_DigestStage21227
import PV_B3P_DigestAssoc227
import PV_B3P_DigestSuffix22227
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false
def digest_suffix_21 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) : Result Digest8Q := do
  let block17 ← lift (Std.Usize.wrapping_add 34#usize 17#usize)
  let i40 ←
    lift (Std.U64.wrapping_shr public1.transition.live_snapshot.next_pair_index
      17#u32)
  let i41 ← lift (i40 &&& 1#u64)
  let digests22 ←
    if i41 = 0#u64
    then
      do
      let i42 ← lift (Std.Usize.wrapping_mul block17 16#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i42
      let a ← reference_terminal.empty_root 17#usize
      reference_terminal.add_digest_binding output q3 openings.z
        aspis_statement.poseidon2.RATE a true
    else
      do
      let i42 ← lift (Std.Usize.wrapping_mul block17 16#usize)
      let i43 ← lift (Std.Usize.wrapping_add i42 12#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i43
      let a ←
        reference_terminal.digest227 public1.transition.live_snapshot.frontier
          17#usize
      reference_terminal.add_digest_binding output q3 openings.z 0#usize a
        false
  digest_suffix_22 public1 openings selectors digests22

attribute [local irreducible] reference_terminal.add_digest_binding reference_copy_terminal.Selectors.row reference_terminal.empty_root reference_terminal.digest227 reference_terminal.bounded_append_carry digest_suffix_22

theorem digest_suffix_21_equation (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_suffix_21 public1 openings selectors output = digest_stage_21 public1 openings selectors output >>= digest_suffix_22 public1 openings selectors := by
  simp only [digest_suffix_21,digest_stage_21,digest_assoc]

theorem digest_suffix_21_success (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    Success (digest_suffix_21 public1 openings selectors output) := by
  rw [digest_suffix_21_equation]
  apply bind
  · exact digest_stage_21_success public1 openings selectors output
  intro next
  exact digest_suffix_22_success public1 openings selectors next

#print axioms digest_suffix_21_equation
#print axioms digest_suffix_21_success
end PV_B3P_Success227
