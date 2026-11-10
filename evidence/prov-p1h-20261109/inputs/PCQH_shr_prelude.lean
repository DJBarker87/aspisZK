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
