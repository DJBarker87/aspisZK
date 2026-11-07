import NMN_241Continuation
set_option autoImplicit false
noncomputable section
namespace NMN_241Prefix
open Aeneas Aeneas.Std Result AdapterRw NLE_Owned
/-- Exact fixed source prefix, ending at the242 occurrence. -/
def run (ops : Ops) (initial : State)
 (validateReply : Result (core.result.Result Validated PE))
  :
  Run (core.result.Result Unit solana_program_error.ProgramError)
  := do
  let program_id := initial.frame.program
  let accounts := initial.frame.accounts
  let data := initial.frame.data
  let current_slot := initial.frame.slot
  let i := Slice.len accounts
  if i != 7#usize
  then
    pure (core.result.Result.Err
      solana_program_error.ProgramError.InvalidInstructionData)
  else
    let o ←
      core.slice.Slice.get (core.slice.index.SliceIndexRangeToUsizeSlice
        Std.U8) data { «end» := 4#usize }
    let s ←
      core.array.Array.index (core.ops.index.IndexSlice
        ((core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice ops)
        Std.U8))
        aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC
        ()
    let b ←
      core.cmp.PartialEq.ne.trait_default
        ((core.option.Option.Insts.CoreCmpPartialEqOption ops)
        (core.cmp.PartialEqShared (Slice.Insts.CoreCmpPartialEqSlice
        core.cmp.PartialEqU8))) o (some s)
    if b
    then
      pure (core.result.Result.Err
        solana_program_error.ProgramError.InvalidInstructionData)
    else
      NMN_241Continuation.entered ops initial validateReply

theorem factor (ops : Ops) (initial : State) (reply : Result (core.result.Result Validated PE)) :
 NMN_241ValueFold.G ops initial reply=run ops initial reply := rfl
/-- A rejected account count has no entered child or observable suffix. -/
theorem wrong_count (ops : Ops) (initial : State) (reply : Result (core.result.Result Validated PE))
 (wrong : (Slice.len initial.frame.accounts != 7#usize)=true) :
 run ops initial reply = ⟨.ok (.Err solana_program_error.ProgramError.InvalidInstructionData),[]⟩ := by
 simp [run,wrong]
 rfl
#print run
#print factor
#print wrong_count
#print axioms factor
#print axioms wrong_count
end NMN_241Prefix
