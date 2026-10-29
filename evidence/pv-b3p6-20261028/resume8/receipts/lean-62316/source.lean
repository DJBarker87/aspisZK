import PV_B3P_DigestStage23227
import PV_B3P_DigestAssoc227
import PV_B3P_DigestSuffix24227
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false
def digest_suffix_23 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) : Result Digest8Q := do
  let block19 ← lift (Std.Usize.wrapping_add 34#usize 19#usize)
  let i44 ←
    lift (Std.U64.wrapping_shr public1.transition.live_snapshot.next_pair_index
      19#u32)
  let i45 ← lift (i44 &&& 1#u64)
  let digests24 ←
    if i45 = 0#u64
    then
      do
      let i46 ← lift (Std.Usize.wrapping_mul block19 16#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i46
      let a ← reference_terminal.empty_root 19#usize
      reference_terminal.add_digest_binding output q3 openings.z
        aspis_statement.poseidon2.RATE a true
    else
      do
      let i46 ← lift (Std.Usize.wrapping_mul block19 16#usize)
      let i47 ← lift (Std.Usize.wrapping_add i46 12#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i47
      let a ←
        reference_terminal.digest227 public1.transition.live_snapshot.frontier
          19#usize
      reference_terminal.add_digest_binding output q3 openings.z 0#usize a
        false
  digest_suffix_24 public1 openings selectors digests24

attribute [local irreducible] reference_terminal.add_digest_binding reference_copy_terminal.Selectors.row reference_terminal.empty_root reference_terminal.digest227 reference_terminal.bounded_append_carry digest_suffix_24

theorem digest_suffix_23_equation (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_suffix_23 public1 openings selectors output = digest_stage_23 public1 openings selectors output >>= digest_suffix_24 public1 openings selectors := by
  simp only [digest_suffix_23,digest_stage_23,digest_assoc]

theorem digest_suffix_23_success (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    Success (digest_suffix_23 public1 openings selectors output) := by
  rw [digest_suffix_23_equation]
  apply bind
  · exact digest_stage_23_success public1 openings selectors output
  intro next
  exact digest_suffix_24_success public1 openings selectors next

#print axioms digest_suffix_23_equation
#print axioms digest_suffix_23_success
end PV_B3P_Success227
