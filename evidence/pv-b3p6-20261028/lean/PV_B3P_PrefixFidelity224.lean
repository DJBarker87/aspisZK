import PV_B3P_PrefixEmission224
namespace PV_B3P_PrefixFidelity224
open Aeneas Aeneas.Std PV_B3P_224Prefix
set_option autoImplicit false

-- Four sparse, changing writes; ordinary compiled evaluation, no proof credit.
-- Only the fixed sixteen-limb zero tuple is evaluated, with lambda zero.
def empty : aspis_statement.logup.CopyLogUpRow :=
  { producer_values := Array.repeat 2#usize aspis_core.field.QM31.ZERO
    producer_weights := Array.repeat 2#usize aspis_core.field.M31.ZERO
    consumer_values := Array.repeat 2#usize aspis_core.field.QM31.ZERO
    consumer_weights := Array.repeat 2#usize aspis_core.field.M31.ZERO }
def view : prefix224.View :=
  { stable := Array.repeat 16#usize (Array.repeat 1024#usize none)
    late := Array.repeat 16#usize (Array.repeat 1024#usize none)
    withdrawal := false }
def tuple : aspis_statement.pool_v1.pair_trace.PoolV1PairCopyTupleV1 :=
  { row := 1023#u16
    limbs := Array.repeat 16#usize .Zero }
def words (x : aspis_core.field.QM31) : List Nat := [x.c0.a.val,x.c0.b.val,x.c1.a.val,x.c1.b.val]
def rowWords (x : aspis_statement.logup.CopyLogUpRow) : List Nat :=
  (x.producer_values.val ++ x.consumer_values.val).flatMap words ++
    x.producer_weights.val.map UScalar.val ++ x.consumer_weights.val.map UScalar.val

def writeCases : Result (List (List Nat)) := do
  let rows := Array.repeat 1024#usize empty
  let a ← prefix224.side rows view tuple 7#u32 1#u32 aspis_core.field.QM31.ZERO false
  match a with
  | .Err _ => .fail .panic
  | .Ok rows =>
    let a0 ← Array.index_usize rows 1023#usize
    let b ← prefix224.side rows view tuple 11#u32 0#u32 aspis_core.field.QM31.ZERO false
    match b with
    | .Err _ => .fail .panic
    | .Ok rows =>
      let a1 ← Array.index_usize rows 1023#usize
      let c ← prefix224.side rows view tuple 13#u32 0#u32 aspis_core.field.QM31.ZERO false
      match c with
      | .Err _ => .fail .panic
      | .Ok rows =>
        let a2 ← Array.index_usize rows 1023#usize
        let d ← prefix224.side rows view tuple 17#u32 1#u32 aspis_core.field.QM31.ZERO true
        match d with
        | .Err _ => .fail .panic
        | .Ok rows =>
          let a3 ← Array.index_usize rows 1023#usize
          .ok [rowWords a0,rowWords a1,rowWords a2,rowWords a3]
#eval match writeCases with
  | .ok xs => IO.println s!"D188-prefix224-cases={xs}"
  | .fail _ => IO.println "D188-prefix224-failed"
  | .div => IO.println "D188-prefix224-diverged"
end PV_B3P_PrefixFidelity224
