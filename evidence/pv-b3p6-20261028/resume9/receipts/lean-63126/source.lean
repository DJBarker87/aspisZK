import PV_B3P_DigestStage11227
import PV_B3P_ReadFunctions9227
namespace PV_B3P_Binding9227
open Aeneas Aeneas.Std PV_B3P_227
open PV_B3P_Success227
set_option autoImplicit false

def digest_read_context9_11 (source_read : Array (Array U32 8#usize) 20#usize → Usize → Result (Array U32 8#usize)) (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors)
    (output : Digest8Q) : Result Digest8Q :=  do
  let block7 ← lift (Std.Usize.wrapping_add 34#usize 7#usize)
  let i20 ←
    lift (Std.U64.wrapping_shr public1.transition.live_snapshot.next_pair_index
      7#u32)
  let i21 ← lift (i20 &&& 1#u64)
  if i21 = 0#u64
  then
    do
    let i22 ← lift (Std.Usize.wrapping_mul block7 16#usize)
    let q3 ← reference_copy_terminal.Selectors.row selectors i22
    let a ← reference_terminal.empty_root 7#usize
    reference_terminal.add_digest_binding output q3 openings.z
      aspis_statement.poseidon2.RATE a true
  else
    do
    let i22 ← lift (Std.Usize.wrapping_mul block7 16#usize)
    let i23 ← lift (Std.Usize.wrapping_add i22 12#usize)
    let q3 ← reference_copy_terminal.Selectors.row selectors i23
    let a ←
      source_read public1.transition.live_snapshot.frontier
        7#usize
    reference_terminal.add_digest_binding output q3 openings.z 0#usize a
      false

def digest_direct_stage9_11 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) : Result Digest8Q :=
  digest_read_context9_11 (fun values i => Array.index_usize values i) public1 openings selectors output

theorem digest_stage_read_binding9_11 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_stage_11 public1 openings selectors output =
      digest_direct_stage9_11 public1 openings selectors output :=
  congrArg (fun source_read => digest_read_context9_11 source_read public1 openings selectors output) digest_function_binding
#print axioms digest_stage_read_binding9_11
end PV_B3P_Binding9227
