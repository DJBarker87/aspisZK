import Hiq_ReleaseRoute
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hiq_DispatchSource
open Aeneas Aeneas.Std Result
abbrev Key := AdapterRw.solana_pubkey.Pubkey
abbrev PE := AdapterRw.solana_program_error.ProgramError

/-- Native AccountInfo is abstract here because the emitted dispatcher NEVER
inspects an account. Child boundaries keep the same full account slice. -/
structure Ops (Account : Type) where
  first : Key → Slice Account → Slice U8 → Result (core.result.Result Unit PE)
  second : Key → Slice Account → Slice U8 → Result (core.result.Result Unit PE)
  init : Key → Slice Account → Slice U8 → Result (core.result.Result Unit PE)
  write : Key → Slice Account → Slice U8 → Result (core.result.Result Unit PE)
  finalize : Key → Slice Account → Slice U8 → Result (core.result.Result Unit PE)

def eqU8 {N : Usize} (data : Slice U8) (a : Array U8 N) : Result Bool := by
  classical
  exact ok (decide (data.val = a.val))
def firstByte (data : Slice U8) : Result (Option U8) := ok data.val.head?
def copied (value : Option U8) : Result (Option U8) := ok value
def starts (data pattern : Slice U8) : Result Bool := by
  classical
  exact ok (decide (data.val.take pattern.val.length = pattern.val))

def r1_pool_adapter.process {Account : Type} (ops : Ops Account)
  (program_id : Key)
  (accounts : Slice Account) (data : Slice Std.U8) :
  Result (core.result.Result Unit PE)
  := do
  let o ← firstByte data
  let o1 ← copied o
  match o1 with
  | none =>
    let b ←
      eqU8 data
        (Array.make 2#usize [ 3#u8, 10#u8 ])
    if b
    then ops.first program_id accounts data
    else
      let b1 ←
        eqU8 data
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
        eqU8 data
          (Array.make 2#usize [ 3#u8, 10#u8 ])
      if b
      then ops.first program_id accounts data
      else
        let b1 ←
          eqU8 data
            (Array.make 2#usize [ 3#u8, 11#u8 ])
        if b1
        then ops.first program_id accounts data
        else ops.second program_id accounts data

/-- [aspis_r1_cost_probe_program::pool_route::admitted]:
    Source: 'programs/r1-cost-probe/src/pool_route.rs', lines 3:0-5:1 -/
def pool_route.admitted (data : Slice Std.U8) : Result Bool := do
  let b ←
    eqU8 data
      (Array.make 2#usize [ 3#u8, 10#u8 ])
  if b
  then ok true
  else
    let b1 ←
      eqU8 data
        (Array.make 2#usize [ 3#u8, 11#u8 ])
    if b1
    then ok true
    else
      let s ←
        lift (Array.to_slice
          (Array.make 4#usize [ 65#u8, 83#u8, 81#u8, 56#u8 ]))
      starts data s

/-- [aspis_r1_cost_probe_program::process_r1_cost_probe_instruction]:
    Source: 'programs/r1-cost-probe/src/lib.rs', lines 56:0-90:1
    Visibility: public -/
def process_r1_cost_probe_instruction {Account : Type} (ops : Ops Account)
  (program_id : Key)
  (accounts : Slice Account) (data : Slice Std.U8) :
  Result (core.result.Result Unit PE)
  := do
  let b ← pool_route.admitted data
  if b
  then r1_pool_adapter.process ops program_id accounts data
  else
    ok (core.result.Result.Err
      AdapterRw.solana_program_error.ProgramError.InvalidInstructionData)

end AspisR1.Hiq_DispatchSource

end
