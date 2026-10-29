import PV_B3P_DigestStage21227
import PV_B3P_ReadFunctions9227
namespace PV_B3P_Binding9227
open Aeneas Aeneas.Std PV_B3P_227
open PV_B3P_Success227
set_option autoImplicit false

def digest_read_context9_21 (source_read : Array (Array U32 8#usize) 20#usize → Usize → Result (Array U32 8#usize)) (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors)
    (output : Digest8Q) : Result Digest8Q :=  do
  let block17 ← lift (Std.Usize.wrapping_add 34#usize 17#usize)
  let i40 ←
    lift (Std.U64.wrapping_shr public1.transition.live_snapshot.next_pair_index
      17#u32)
  let i41 ← lift (i40 &&& 1#u64)
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
      source_read public1.transition.live_snapshot.frontier
        17#usize
    reference_terminal.add_digest_binding output q3 openings.z 0#usize a
      false

def digest_direct_stage9_21 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) : Result Digest8Q :=
  digest_read_context9_21 (fun values i => Array.index_usize values i) public1 openings selectors output

theorem digest_stage_read_binding9_21 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_stage_21 public1 openings selectors output =
      digest_direct_stage9_21 public1 openings selectors output :=
  congrArg (fun source_read => digest_read_context9_21 source_read public1 openings selectors output) digest_function_binding
#print axioms digest_stage_read_binding9_21
end PV_B3P_Binding9227
