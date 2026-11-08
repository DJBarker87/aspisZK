import NMW_Emitted
set_option autoImplicit false
noncomputable section
namespace NMW_Symbolic
open AspisR1
open Aeneas Aeneas.Std Result
/-- Universal interpretation of opaque call results in the fresh emitted tree.
No account operation occurs before or after the selected child. -/
structure Ops (Account Value : Type) where
 first : Hiq_DispatchSource.Key → Slice Account → Slice U8 → Result Value
 second : Hiq_DispatchSource.Key → Slice Account → Slice U8 → Result Value
 init : Hiq_DispatchSource.Key → Slice Account → Slice U8 → Result Value
 write : Hiq_DispatchSource.Key → Slice Account → Slice U8 → Result Value
 finalize : Hiq_DispatchSource.Key → Slice Account → Slice U8 → Result Value

/- Actual extraction body, with opaque boundaries parameterized and canonical
    types/primitives reused. See NIV_PARAMETERIZATION.json; no template axiom. -/
/-- [aspis_r1_cost_probe_program::r1_pool_adapter::process]:
    Source: 'programs/r1-cost-probe/src/r1_pool_adapter.rs', lines 950:0-962:1 -/
def process {Account Value : Type} (ops : Ops Account Value)
  (program_id : Hiq_DispatchSource.Key)
  (accounts : Slice Account) (data : Slice Std.U8) :
  Result Value
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
def entry {Account Value : Type} (ops : Ops Account Value) (reject : Value)
  (program_id : Hiq_DispatchSource.Key)
  (accounts : Slice Account) (data : Slice Std.U8) :
  Result Value
  := do
  let b ← Hiq_DispatchSource.pool_route.admitted data
  if b
  then process ops program_id accounts data
  else
    ok reject


def scalarOps {Account : Type} (ops : Hiq_DispatchSource.Ops Account) :
 Ops Account (core.result.Result Unit Hiq_DispatchSource.PE) :=
 ⟨ops.first,ops.second,ops.init,ops.write,ops.finalize⟩
/-- Scalar specialization is the actual fresh emitted body, not an endpoint
assumption. The universal opaque interpretation retains every call argument. -/
theorem process_specialize {Account : Type} (ops : Hiq_DispatchSource.Ops Account)
 (p : Hiq_DispatchSource.Key) (a : Slice Account) (d : Slice U8) :
 process (scalarOps ops) p a d = NMW_Emitted.process ops p a d := rfl
theorem entry_specialize {Account : Type} (ops : Hiq_DispatchSource.Ops Account)
 (p : Hiq_DispatchSource.Key) (a : Slice Account) (d : Slice U8) :
 entry (scalarOps ops) (.Err .InvalidInstructionData) p a d =
 NMW_Emitted.entry ops p a d := rfl
#print axioms process_specialize
#print axioms entry_specialize
end NMW_Symbolic
end
