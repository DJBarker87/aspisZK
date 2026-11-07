import NMT_345Frames
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result NMT_stage1_owned
/-- Verbatim E003 continuation at emitted Try occurrence 12; only local
captures are projected from the single complete parent state. -/
def raw12 {W : Type} (c : Calls) (parent : Returned W) : Result Ret := do
 let i7 := alloc.vec.Vec.len parent.checkpoint
 let i8 := Slice.len parent.checkpointData
 if i7 != i8
 then
   ok (core.result.Result.Err
     solana_program_error.ProgramError.InvalidAccountData)
 else ok (core.result.Result.Ok parent.checkpoint)
end NMT_345
