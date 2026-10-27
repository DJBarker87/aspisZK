import XRz_RecordAt
import XRx_TryDriver
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XRz_ParseFold
abbrev State := List (Slice U8) × Usize
def row (n : Nat) : U8 := if h:n<27 then UScalar.ofNat n (by scalar_tac) else 0#u8
def step (bytes : Slice U8) (i : Nat) (s : State) : Result (core.result.Result State r1_wire.Error) := do
 let r ← r1_wire.parse_record_at bytes (row i) s.2
 match r with
 | .Err e => ok (.Err e)
 | .Ok p => ok (.Ok (s.1++[p.1],p.2))
def finish (bytes : Slice U8) (root : Array U8 32#usize) (s : State) :
 Result (core.result.Result r1_wire.Prefix r1_wire.Error) :=
 if s.2 != Slice.len bytes then ok (.Err .TrailingBytes)
 else if h:s.1.length=27 then ok (.Ok ⟨root,⟨s.1,h⟩⟩) else fail .panic

def parse (bytes : Slice U8) : Result (core.result.Result r1_wire.Prefix r1_wire.Error) := do
 if Slice.len bytes < 32#usize then ok (.Err (.Length 0#u8)) else
 let s ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8) bytes {«end»:=32#usize}
 let r ← core.array.TryFromSharedArraySlice.try_from 32#usize s
 match r with
 | .Err _ => ok (.Err (.Length 0#u8))
 | .Ok root =>
  let out ← XRx_StageFold.fold (step bytes) (List.range' 0 27) (.Ok ([],32#usize))
  match out with
  | .Err e => ok (.Err e)
  | .Ok state => finish bytes root state
end XRz_ParseFold
