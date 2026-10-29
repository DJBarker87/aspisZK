import PV_B3P_DigestStage12227
import PV_B3P_ReadFunctions9227
namespace PV_B3P_Binding9227
open Aeneas Aeneas.Std PV_B3P_227
open PV_B3P_Success227
set_option autoImplicit false

def digest_read_context9_12 (source_read : Array (Array U32 8#usize) 20#usize → Usize → Result (Array U32 8#usize)) (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors)
    (output : Digest8Q) : Result Digest8Q :=  do
  let block8 ← lift (Std.Usize.wrapping_add 34#usize 8#usize)
  let i22 ←
    lift (Std.U64.wrapping_shr public1.transition.live_snapshot.next_pair_index
      8#u32)
  let i23 ← lift (i22 &&& 1#u64)
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
      source_read public1.transition.live_snapshot.frontier
        8#usize
    reference_terminal.add_digest_binding output q3 openings.z 0#usize a
      false

def digest_direct_stage9_12 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) : Result Digest8Q :=
  digest_read_context9_12 (fun values i => Array.index_usize values i) public1 openings selectors output

theorem digest_stage_read_binding9_12 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_stage_12 public1 openings selectors output =
      digest_direct_stage9_12 public1 openings selectors output :=
  congrArg (fun source_read => digest_read_context9_12 source_read public1 openings selectors output) digest_function_binding
#print axioms digest_stage_read_binding9_12
end PV_B3P_Binding9227
