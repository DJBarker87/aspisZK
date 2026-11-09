import Aeneas
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section
namespace PCVB_M31

def redBody (P : Std.U32) (x : Std.U64) : Result Std.U32 := do
  let i ← lift (UScalar.cast .U64 P)
  let i1 ← lift (x &&& i)
  let i2 ← x >>> 31#u32
  let x1 ← i1 + i2
  let i3 ← lift (UScalar.cast .U64 P)
  let i4 ← lift (x1 &&& i3)
  let i5 ← x1 >>> 31#u32
  let x2 ← i4 + i5
  let x3 ← lift (UScalar.cast .U32 x2)
  if x3 >= P
  then x3 - P
  else ok x3

def fastBody (P : Std.U32) (x : Std.U64) : Result Std.U32 := do
  let i2 ← lift (UScalar.cast .U64 P)
  let i3 ← lift (x &&& i2)
  let i4 ← x >>> 31#i32
  let s ← i3 + i4
  let i5 ← lift (UScalar.cast .U64 P)
  if s >= i5
  then
    let i6 ← lift (UScalar.cast .U64 P)
    let i7 ← s - i6
    let i8 ← lift (UScalar.cast .U32 i7)
    ok i8
  else let i6 ← lift (UScalar.cast .U32 s)
       ok i6

theorem fast_spec (P : Std.U32) (hP : P.val = 2147483647) (x : Std.U64) (hx : x.val < 2^62) :
    fastBody P x ⦃ r => r.val = (if 2147483647 ≤ x.val % 2^31 + x.val / 2^31 then x.val % 2^31 + x.val / 2^31 - 2147483647 else x.val % 2^31 + x.val / 2^31) ⦄ := by
  unfold fastBody
  step*
  all_goals trace_state
  all_goals sorry

theorem red_spec (P : Std.U32) (hP : P.val = 2147483647) (x : Std.U64) (hx : x.val < 2^62) :
    redBody P x ⦃ r => r.val = (if 2147483647 ≤ x.val % 2^31 + x.val / 2^31 then x.val % 2^31 + x.val / 2^31 - 2147483647 else x.val % 2^31 + x.val / 2^31) ⦄ := by
  unfold redBody
  step*
  all_goals trace_state
  all_goals sorry
end PCVB_M31
