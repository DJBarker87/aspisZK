-- PCVE_ P3e: domain equality for the transport row family. Fresh (overflow-OFF) text copied from PCQH_L025 source (fresh source sha256 693741a9...).
import Aeneas
import RPz7_FIo_NativeFuns
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace FIo_Native
namespace PRVFresh_RPz7_FIo_NativeFuns_h2
/- PCQH encoding bridge (recorded in PCQH_HAND_MODELS.json / PCQH_CLASSIFICATIONS.json PCQH-C2): with overflow checks OFF the extended Aeneas
   (b59d5188) translates the Rust shift operator `x >> n` on `usize` as `Std.Usize.wrapping_shr x n`, passing the right operand at ITS OWN Rust type
   (`9#i32`, or a `Usize`), whereas the library signature is `Usize.wrapping_shr : Usize -> U32 -> Usize`, so the emitted text does not elaborate.
   The bridge below gives the emitted call the Rust meaning: the shift amount is converted by `as u32` (the library's `wrapping_shr` then masks it
   modulo the bit width, which is the unchecked-`>>` behaviour of Rust with overflow checks off). Name resolution inside the fresh namespace prefers this
   definition; it delegates to the library function. -/
class ShrAmt (α : Type) where
  toU32 : α → Std.U32
instance : ShrAmt Std.I32 := ⟨fun y => IScalar.hcast .U32 y⟩
instance : ShrAmt Std.Usize := ⟨fun y => UScalar.cast .U32 y⟩
def Std.Usize.wrapping_shr {α : Type} [ShrAmt α] (x : Std.Usize) (y : α) : Std.Usize :=
  _root_.Aeneas.Std.Usize.wrapping_shr x (ShrAmt.toU32 y)
def Std.Usize.wrapping_shl {α : Type} [ShrAmt α] (x : Std.Usize) (y : α) : Std.Usize :=
  _root_.Aeneas.Std.Usize.wrapping_shl x (ShrAmt.toU32 y)



/-- [aspis_r1_cost_probe::transport::{impl core::cmp::PartialEq<aspis_r1_cost_probe::transport::Variant> for aspis_r1_cost_probe::transport::Variant}::eq]:
    Source: 'crates/aspis-r1-cost-probe/src/transport.rs', lines 2:26-2:35
    Visibility: public -/
def transport.Variant.Insts.CoreCmpPartialEqVariant.eq
  (self : transport.Variant) (other : transport.Variant) : Result Bool := do
  let self1 := read_discriminant self
  let other1 := read_discriminant other
  ok (self1 = other1)

/-- [aspis_r1_cost_probe::transport::TAU]
    Source: 'crates/aspis-r1-cost-probe/src/transport.rs', lines 4:0-4:44
    Visibility: public -/
@[global_simps, irreducible]
def transport.TAU : Array Std.Usize 5#usize :=
  Array.make 5#usize [ 3#usize, 4#usize, 2#usize, 0#usize, 1#usize ]

/-- [aspis_r1_cost_probe::transport::{aspis_r1_cost_probe::transport::Variant}::row]: loop body 0:
    Source: 'crates/aspis-r1-cost-probe/src/transport.rs', lines 13:8-13:62
    Visibility: public -/
def transport.Variant.row_loop.body
  (j : Std.Usize) (iter : core.ops.range.Range Std.Usize) (out : Std.Usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × Std.Usize)
    Std.Usize)
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done out)
  | some d =>
    let i ← lift (Std.Usize.wrapping_mul 2#usize d)
    let i1 ← lift (Std.Usize.wrapping_shr j i)
    let i2 ← lift (i1 &&& 3#usize)
    let i3 ← Array.index_usize transport.TAU d
    let i4 ← lift (Std.Usize.wrapping_mul 2#usize i3)
    let i5 ← lift (Std.Usize.wrapping_shl i2 i4)
    let out1 ← lift (out ||| i5)
    ok (cont (iter1, out1))

/-- [aspis_r1_cost_probe::transport::{aspis_r1_cost_probe::transport::Variant}::row]: loop 0:
    Source: 'crates/aspis-r1-cost-probe/src/transport.rs', lines 13:8-13:62
    Visibility: public -/
def transport.Variant.row_loop
  (iter : core.ops.range.Range Std.Usize) (j : Std.Usize) (out : Std.Usize) :
  Result Std.Usize
  := do
  loop
    (fun (iter1, out1) => transport.Variant.row_loop.body j iter1 out1)
    (iter, out)

/-- [aspis_r1_cost_probe::transport::{aspis_r1_cost_probe::transport::Variant}::row]:
    Source: 'crates/aspis-r1-cost-probe/src/transport.rs', lines 10:4-15:5
    Visibility: public -/
def transport.Variant.row
  (self : transport.Variant) (j : Std.Usize) : Result Std.Usize := do
  let b ←
    transport.Variant.Insts.CoreCmpPartialEqVariant.eq self transport.Variant.D
  if b
  then
    let a ← aspis_core.r0.transport.COEFFICIENT_TO_ROW
    let i ← Array.index_usize a j
    ok (UScalar.cast .Usize i)
  else
    transport.Variant.row_loop { start := 0#usize, «end» := 5#usize } j
      0#usize

end PRVFresh_RPz7_FIo_NativeFuns_h2
end FIo_Native
