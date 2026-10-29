import PV_B3P_DigestStage08227
import PV_B3P_ReadFunctions9227
namespace PV_B3P_Binding9227
open Aeneas Aeneas.Std PV_B3P_227
open PV_B3P_Success227
set_option autoImplicit false

def digest_read_context9_08 (source_read : Array (Array U32 8#usize) 20#usize → Usize → Result (Array U32 8#usize)) (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors)
    (output : Digest8Q) : Result Digest8Q :=  do
  let block4 ← lift (Std.Usize.wrapping_add 34#usize 4#usize)
  let i14 ←
    lift (Std.U64.wrapping_shr public1.transition.live_snapshot.next_pair_index
      4#u32)
  let i15 ← lift (i14 &&& 1#u64)
  if i15 = 0#u64
  then
    do
    let i16 ← lift (Std.Usize.wrapping_mul block4 16#usize)
    let q3 ← reference_copy_terminal.Selectors.row selectors i16
    let a ← reference_terminal.empty_root 4#usize
    reference_terminal.add_digest_binding output q3 openings.z
      aspis_statement.poseidon2.RATE a true
  else
    do
    let i16 ← lift (Std.Usize.wrapping_mul block4 16#usize)
    let i17 ← lift (Std.Usize.wrapping_add i16 12#usize)
    let q3 ← reference_copy_terminal.Selectors.row selectors i17
    let a ←
      source_read public1.transition.live_snapshot.frontier
        4#usize
    reference_terminal.add_digest_binding output q3 openings.z 0#usize a
      false

def digest_direct_stage9_08 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) : Result Digest8Q :=
  digest_read_context9_08 (fun values i => Array.index_usize values i) public1 openings selectors output

theorem digest_stage_read_binding9_08 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_stage_08 public1 openings selectors output =
      digest_direct_stage9_08 public1 openings selectors output :=
  congrArg (fun source_read => digest_read_context9_08 source_read public1 openings selectors output) digest_function_binding
#print axioms digest_stage_read_binding9_08
end PV_B3P_Binding9227
