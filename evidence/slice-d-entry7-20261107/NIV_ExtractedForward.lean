import Hiq_DispatchRelease
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIV_ExtractedForward
open Aeneas Aeneas.Std Result
/- Actual extraction body, with opaque boundaries parameterized and canonical
    types/primitives reused. See NIV_PARAMETERIZATION.json; no template axiom. -/
/-- [aspis_r1_cost_probe_program::r1_pool_adapter::process]:
    Source: 'programs/r1-cost-probe/src/r1_pool_adapter.rs', lines 950:0-962:1 -/
def process {Account : Type} (ops : Hiq_DispatchSource.Ops Account)
  (program_id : Hiq_DispatchSource.Key)
  (accounts : Slice Account) (data : Slice Std.U8) :
  Result (core.result.Result Unit Hiq_DispatchSource.PE)
  := do
  let o ← Hiq_DispatchSource.firstByte data
  let o1 ← Hiq_DispatchSource.copied o
  match o1 with
  | none =>
    let b ←
      Hiq_DispatchSource.eqU8 data
        (Array.make 2#usize [ 3#u8, 10#u8 ])
    if b
    then ops.first program_id accounts data
    else
      let b1 ←
        Hiq_DispatchSource.eqU8 data
          (Array.make 2#usize [ 3#u8, 11#u8 ])
      if b1
      then ops.first program_id accounts data
      else ops.second program_id accounts data
  | some i =>
    match i with
    | 4#uscalar => ops.init program_id accounts data
    | 5#uscalar => ops.write program_id accounts data
    | 6#uscalar => ops.finalize program_id accounts data
    | _ =>
      let b ←
        Hiq_DispatchSource.eqU8 data
          (Array.make 2#usize [ 3#u8, 10#u8 ])
      if b
      then ops.first program_id accounts data
      else
        let b1 ←
          Hiq_DispatchSource.eqU8 data
            (Array.make 2#usize [ 3#u8, 11#u8 ])
        if b1
        then ops.first program_id accounts data
        else ops.second program_id accounts data

/-- [aspis_r1_cost_probe_program::process_r1_cost_probe_instruction]:
    Source: 'programs/r1-cost-probe/src/lib.rs', lines 56:0-90:1
    Visibility: public -/
def entry {Account : Type} (ops : Hiq_DispatchSource.Ops Account)
  (program_id : Hiq_DispatchSource.Key)
  (accounts : Slice Account) (data : Slice Std.U8) :
  Result (core.result.Result Unit Hiq_DispatchSource.PE)
  := do
  let b ← Hiq_DispatchSource.pool_route.admitted data
  if b
  then process ops program_id accounts data
  else
    ok (core.result.Result.Err
      AdapterRw.solana_program_error.ProgramError.InvalidInstructionData)


theorem process_source {Account : Type} (ops : Hiq_DispatchSource.Ops Account)
    (p : Hiq_DispatchSource.Key) (a : Slice Account) (d : Slice U8) :
    process ops p a d = Hiq_DispatchSource.r1_pool_adapter.process ops p a d := rfl

theorem entry_source {Account : Type} (ops : Hiq_DispatchSource.Ops Account)
    (p : Hiq_DispatchSource.Key) (a : Slice Account) (d : Slice U8) :
    entry ops p a d = Hiq_DispatchSource.process_r1_cost_probe_instruction ops p a d := rfl

/-- Complete result, including foreign error payloads, divergence and failure;
    all three descriptors are unchanged at the selected child boundary. -/
theorem forwarding {Account : Type} (ops : Hiq_DispatchSource.Ops Account)
    (p : Hiq_DispatchSource.Key) (a : Slice Account) (d : Slice U8) :
    entry ops p a d = match Hiq_ReleaseRoute.route d with
      | .first => ops.first p a d
      | .second => ops.second p a d
      | .reject => ok (.Err AdapterRw.solana_program_error.ProgramError.InvalidInstructionData) := by
  rw [entry_source]
  exact Hiq_DispatchRelease.source ops p a d

#print axioms process_source
#print axioms entry_source
#print axioms forwarding
end AspisR1.NIV_ExtractedForward
end
