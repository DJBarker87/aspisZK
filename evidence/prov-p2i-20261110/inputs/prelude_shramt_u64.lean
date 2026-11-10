/- PCUI encoding bridge (hand model ShrAmt, verified for overflow-checks-OFF only: evidence/shramt-20261110/NPE_SHRAMT_CHECK.md; same bridge as PCQH).
   The extended Aeneas emits the OFF translation of Rust `x << n` / `x >> n` on u64 as `Std.U64.wrapping_shl/shr x n` with the amount at ITS OWN Rust type
   (`8#i32`), whereas the library signature takes a U32, so the emitted text does not elaborate. Name resolution inside the fresh namespace prefers these
   definitions; they delegate to the library function with the amount converted `as u32`. Used only for definitions whose required configuration is OFF. -/
class ShrAmt (α : Type) where
  toU32 : α → Std.U32
instance : ShrAmt Std.I32 := ⟨fun y => IScalar.hcast .U32 y⟩
instance : ShrAmt Std.Usize := ⟨fun y => UScalar.cast .U32 y⟩
def Std.U64.wrapping_shl {α : Type} [ShrAmt α] (x : Std.U64) (y : α) : Std.U64 :=
  _root_.Aeneas.Std.U64.wrapping_shl x (ShrAmt.toU32 y)
def Std.U64.wrapping_shr {α : Type} [ShrAmt α] (x : Std.U64) (y : α) : Std.U64 :=
  _root_.Aeneas.Std.U64.wrapping_shr x (ShrAmt.toU32 y)
