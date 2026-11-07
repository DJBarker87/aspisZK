import PCI_DepositActual.Types
import AdapterRwModel
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCI_DepositActual
namespace External
def eqLoop {T U : Type} (cmp : core.cmp.PartialEq T U) : List T → List U → Result Bool
  | [],[] => ok true
  | x::xs,y::ys => do
    let same ← cmp.eq x y
    if same then eqLoop cmp xs ys else ok false
  | _,_ => ok false
end External

def Slice.Insts.CoreCmpPartialEqArray.ne
    {T U : Type} {N : Usize} (cmp : core.cmp.PartialEq T U)
    (xs : Aeneas.Std.Slice T) (ys : Array U N) : Result Bool := do
  if xs.length≠ys.length then ok true
  else
    let same ← External.eqLoop cmp xs.val ys.val
    ok (!same)
abbrev core.option.Option.ok_or := @AdapterRw.core.option.Option.ok_or
abbrev core.result.Result.map_err := @AspisR1AdapterReconstruct.core.result.Result.map_err

def aspis_statement.atomic_statement.decode_digest_canonical (bytes : Array U8 32#usize) :=
  AspisR1TerminalDecoder.atomic_statement.decode_digest_canonical bytes

def aspis_statement.pool_v1.deposit.POOL_V1_ENCRYPTED_NOTE_PAYLOAD_MAX_BYTES : Result Usize := ok 512#usize
def aspis_statement.spend.VALUE_LIMIT : Result U32 := ok 1073741824#u32
end PCI_DepositActual
