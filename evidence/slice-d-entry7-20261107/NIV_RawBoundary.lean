import NIV_ExtractedForward
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIV_RawBoundary
open Aeneas Aeneas.Std Result
/-- Every opaque external retained as an explicit boundary; no axiom template
    is loaded. Only the concrete U8 instantiations reached by this body occur. -/
structure Boundaries (Account : Type) extends Hiq_DispatchSource.Ops Account where
  head : Slice U8 → Result (Option U8)
  copy : Option U8 → Result (Option U8)
  eq : {N : Usize} → Slice U8 → Array U8 N → Result Bool
  admitted : Slice U8 → Result Bool

def profile {Account : Type} (ops : Hiq_DispatchSource.Ops Account) : Boundaries Account where
  toOps := ops
  head := Hiq_DispatchSource.firstByte
  copy := Hiq_DispatchSource.copied
  eq := Hiq_DispatchSource.eqU8
  admitted := Hiq_DispatchSource.pool_route.admitted

/-- [aspis_r1_cost_probe_program::r1_pool_adapter::process]:
    Source: 'programs/r1-cost-probe/src/r1_pool_adapter.rs', lines 950:0-962:1 -/
def process {Account : Type} (ops : Boundaries Account)
  (program_id : Hiq_DispatchSource.Key)
  (accounts : Slice Account) (data : Slice Std.U8) :
  Result (core.result.Result Unit Hiq_DispatchSource.PE)
  := do
  let o ← ops.head data
  let o1 ← ops.copy o
  match o1 with
  | none =>
    let b ←
      ops.eq data
        (Array.make 2#usize [ 3#u8, 10#u8 ])
    if b
    then ops.first program_id accounts data
    else
      let b1 ←
        ops.eq data
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
        ops.eq data
          (Array.make 2#usize [ 3#u8, 10#u8 ])
      if b
      then ops.first program_id accounts data
      else
        let b1 ←
          ops.eq data
            (Array.make 2#usize [ 3#u8, 11#u8 ])
        if b1
        then ops.first program_id accounts data
        else ops.second program_id accounts data

/-- [aspis_r1_cost_probe_program::process_r1_cost_probe_instruction]:
    Source: 'programs/r1-cost-probe/src/lib.rs', lines 56:0-90:1
    Visibility: public -/
def entry {Account : Type} (ops : Boundaries Account)
  (program_id : Hiq_DispatchSource.Key)
  (accounts : Slice Account) (data : Slice Std.U8) :
  Result (core.result.Result Unit Hiq_DispatchSource.PE)
  := do
  let b ← ops.admitted data
  if b
  then process ops program_id accounts data
  else
    ok (core.result.Result.Err
      AdapterRw.solana_program_error.ProgramError.InvalidInstructionData)


/-- Profile specialization is a separate fact from realization of the opaque
    Rust primitive boundaries. Native realization is recorded OPEN. -/
theorem process_profile {Account : Type} (ops : Hiq_DispatchSource.Ops Account)
    (p : Hiq_DispatchSource.Key) (a : Slice Account) (d : Slice U8) :
    process (profile ops) p a d = NIV_ExtractedForward.process ops p a d := rfl

theorem entry_profile {Account : Type} (ops : Hiq_DispatchSource.Ops Account)
    (p : Hiq_DispatchSource.Key) (a : Slice Account) (d : Slice U8) :
    entry (profile ops) p a d = NIV_ExtractedForward.entry ops p a d := rfl

#print axioms process_profile
#print axioms entry_profile
end AspisR1.NIV_RawBoundary
end
