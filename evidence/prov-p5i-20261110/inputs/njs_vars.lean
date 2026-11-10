variable (NJS_call_0 : ∀ {T : Type} {U : Type} {N : Std.Usize} (cmpPartialEqInst : core.cmp.PartialEq
  T U),
(Slice T) → (Array U N) → Result Bool)

variable (NJS_call_1 : ∀ {T : Type} {U : Type} {N : Std.Usize} (cmpPartialEqInst : core.cmp.PartialEq
  T U),
(Slice T) → (Array U N) → Result Bool)

variable (NJS_call_2 : ∀ {Self : Type} {F : Type} {Clause0_Item : Type} (IteratorInst :
  core.iter.traits.iterator.Iterator Self Clause0_Item)
  (opsfunctionFnMutFTupleClause0_ItemBoolInst : core.ops.function.FnMut F
  Clause0_Item Bool),
Self → F → Result (Bool × Self))

variable (NJS_call_3 : ∀ {T : Type} {F : Type} (opsfunctionFnMutFTupleSharedATBoolInst :
  core.ops.function.FnMut F T Bool),
(core.slice.iter.Iter T) → F → Result (Bool × (core.slice.iter.Iter T)))

variable (NJS_call_4 : (Array Std.U8 4#usize) → Result (Option aspis_core.field.M31))

variable (NJS_call_5 : (Slice Std.U8) → Result (Option aspis_core.field.QM31))

variable (NJS_call_6 : Result Std.U8)

variable (NJS_call_7 : Result Std.U8)

variable (NJS_call_8 : ∀ {H : Type} (digestDigest32Inst : aspis_core.digest.Digest32 H),
H → Std.U8 → (Slice Std.U8) → (Array Std.U8 32#usize) → Result (Array
    Std.U8 32#usize))

variable (NJS_call_9 : Std.Usize → Result Std.Usize)

variable (NJS_call_10 : (Slice Std.U8) → Bool → Result (core.result.Result Unit verifier.Error))

variable (NJS_call_11 : (Slice Std.U8) → Result (core.result.Result Unit compact.CodecError))

variable (NJS_call_12 : ∀ {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H),
H → multiproof.Arity → (Array Std.U8 32#usize) → (Array Std.U32
    16#usize) → (Array (Array Std.U8 32#usize) 16#usize) → Std.Usize →
    (Slice Std.U8) → Result (Bool × (Array Std.U32 16#usize) × (Array
    (Array Std.U8 32#usize) 16#usize)))

variable (NJS_call_13 : multiproof.Arity → (Slice Std.U32) → Result (Option Std.Usize))

/- PCWS encoding bridge (the PCQH-C2 ShrAmt pattern, evidence/prov-p1h-20261109/PRVEq_NFN_ExtractedGeometry_h1.lean): with overflow checks OFF the Aeneas translation of the
   Rust shift `x << n` / `x >> n` on `u64` passes the right operand at its own Rust type (`8#i32`), but the library signature is `U64.wrapping_shl : U64 -> U32 -> U64`, so the
   emitted text does not elaborate in the gate library. The bridge converts the amount by `as u32` and delegates to the library function. Verified for overflow-checks-OFF only. -/
class ShrAmt (α : Type) where
  toU32 : α → Std.U32
instance : ShrAmt Std.I32 := ⟨fun y => IScalar.hcast .U32 y⟩
instance : ShrAmt Std.U32 := ⟨fun y => y⟩
def Std.U64.wrapping_shl {α : Type} [ShrAmt α] (x : Std.U64) (y : α) : Std.U64 :=
  _root_.Aeneas.Std.U64.wrapping_shl x (ShrAmt.toU32 y)
def Std.U64.wrapping_shr {α : Type} [ShrAmt α] (x : Std.U64) (y : α) : Std.U64 :=
  _root_.Aeneas.Std.U64.wrapping_shr x (ShrAmt.toU32 y)
