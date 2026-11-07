import PCI_DepositActual.Types
import AdapterRwModel
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCI_DepositActual
/-- Existing trusted-std shared-array conversion and array comparison.
    A length mismatch returns true before any element comparison. -/
def Slice.Insts.CoreCmpPartialEqArray.ne
    {T U : Type} {N : Usize} (cmp : core.cmp.PartialEq T U)
    (xs : Aeneas.Std.Slice T) (ys : Array U N) : Result Bool := do
  let converted ← core.array.TryFromSharedArraySlice.try_from N xs
  match converted with
  | .Ok arr => core.array.equality.PartialEqArray.ne cmp arr ys
  | .Err _ => ok true

abbrev core.option.Option.ok_or := @AdapterRw.core.option.Option.ok_or
abbrev core.result.Result.map_err := @AspisR1AdapterReconstruct.core.result.Result.map_err

def aspis_statement.atomic_statement.decode_digest_canonical (bytes : Array U8 32#usize) :=
  AspisR1TerminalDecoder.atomic_statement.decode_digest_canonical bytes

def aspis_statement.pool_v1.deposit.POOL_V1_ENCRYPTED_NOTE_PAYLOAD_MAX_BYTES : Result Usize := ok 512#usize
def aspis_statement.spend.VALUE_LIMIT : Result U32 := ok 1073741824#u32
end PCI_DepositActual
