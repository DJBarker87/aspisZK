import Aeneas

/- Exact declaration slice from the pinned Aeneas output. No backend axioms. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error
namespace S7OwnedP6Scalar
def residue_scalar_owned
  (raw1 : Std.U64) (limb : Std.U32) (basis : Std.U32) (flush : Bool) :
  Result Std.U64
  := do
  let i ← lift (core.convert.num.FromU64U32.from limb)
  let i1 ← lift (core.convert.num.FromU64U32.from basis)
  let i2 ← i * i1
  let updated ← raw1 + i2
  if flush
  then
    let i3 ← lift (updated &&& 2147483647#u64)
    let i4 ← updated >>> 31#i32
    i3 + i4
  else ok updated


end S7OwnedP6Scalar
