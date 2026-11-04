import NFF_ProductCall
import NFE_NFC_RawAssociation
set_option autoImplicit false
namespace AspisR1.NFF_LoggedRaw
open Aeneas Aeneas.Std Result
def run
  (oracle : NFF_ProductCall.Oracle)
  (self : FIo_QRaw.canonical.Q) (rhs : FIo_QRaw.canonical.Q) :
  Result (Array Std.U64 4#usize)
  := do
  let a ←
    core.array.Array.map
      FIo_QRaw.canonical.Q.raw.closure.Insts.CoreOpsFunctionFnMutTupleU32U64 self ()
  let a1 ← Array.index_usize a 0#usize
  let b ← Array.index_usize a 1#usize
  let c ← Array.index_usize a 2#usize
  let d ← Array.index_usize a 3#usize
  let a2 ←
    core.array.Array.map
      FIo_QRaw.canonical.Q.raw.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U64 rhs ()
  let e ← Array.index_usize a2 0#usize
  let f ← Array.index_usize a2 1#usize
  let g ← Array.index_usize a2 2#usize
  let h ← Array.index_usize a2 3#usize
  let i ← NFF_ProductCall.call oracle c g
  let i1 ← FIo_QRaw.canonical.Q.raw.PP
  let i2 ← lift (core.num.U64.wrapping_add i i1)
  let i3 ← NFF_ProductCall.call oracle d h
  let i4 ← lift (core.num.U64.wrapping_sub i2 i3)
  let u ←
    FIo_QRaw.canonical.Q.raw.closure_2.Insts.CoreOpsFunctionFnTupleU64U64.call () i4
  let i5 ← NFF_ProductCall.call oracle c h
  let i6 ← NFF_ProductCall.call oracle d g
  let i7 ← lift (core.num.U64.wrapping_add i5 i6)
  let v ←
    FIo_QRaw.canonical.Q.raw.closure_2.Insts.CoreOpsFunctionFnTupleU64U64.call () i7
  let i8 ← NFF_ProductCall.call oracle a1 e
  let i9 ← lift (core.num.U64.wrapping_add i8 i1)
  let i10 ← NFF_ProductCall.call oracle b f
  let i11 ← lift (core.num.U64.wrapping_sub i9 i10)
  let i12 ← 2#u64 * u
  let i13 ← lift (core.num.U64.wrapping_add i11 i12)
  let i14 ← lift (core.convert.num.FromU64U32.from FIo_QRaw.canonical.P)
  let i15 ← 3#u64 * i14
  let i16 ← lift (core.num.U64.wrapping_add i13 i15)
  let i17 ← lift (core.num.U64.wrapping_sub i16 v)
  let i18 ← NFF_ProductCall.call oracle a1 f
  let i19 ← NFF_ProductCall.call oracle b e
  let i20 ← lift (core.num.U64.wrapping_add i18 i19)
  let i21 ← lift (core.num.U64.wrapping_add i20 u)
  let i22 ← 2#u64 * v
  let i23 ← lift (core.num.U64.wrapping_add i21 i22)
  let i24 ← NFF_ProductCall.call oracle a1 g
  let i25 ← NFF_ProductCall.call oracle c e
  let i26 ← lift (core.num.U64.wrapping_add i24 i25)
  let i27 ← 2#u64 * i1
  let i28 ← lift (core.num.U64.wrapping_add i26 i27)
  let i29 ← NFF_ProductCall.call oracle b h
  let i30 ← lift (core.num.U64.wrapping_sub i28 i29)
  let i31 ← NFF_ProductCall.call oracle d f
  let i32 ← lift (core.num.U64.wrapping_sub i30 i31)
  let i33 ← NFF_ProductCall.call oracle a1 h
  let i34 ← NFF_ProductCall.call oracle b g
  let i35 ← lift (core.num.U64.wrapping_add i33 i34)
  let i36 ← NFF_ProductCall.call oracle c f
  let i37 ← lift (core.num.U64.wrapping_add i35 i36)
  let i38 ← NFF_ProductCall.call oracle d e
  let i39 ← lift (core.num.U64.wrapping_add i37 i38)
  ok (Array.make 4#usize [ i17, i23, i32, i39 ])


/-- All sixteen reached product continuations are replaced in source order.
The rest is the unchanged emitted raw expression, including checked constant
products and wrapping additions/subtractions. -/
theorem replay (oracle : NFF_ProductCall.Oracle) (law : NFF_ProductCall.Law oracle)
    (a b : FIo_QRaw.canonical.Q) : run oracle a b=FIo_QRaw.canonical.Q.raw a b := by
  simp only [run,FIo_QRaw.canonical.Q.raw,NFF_ProductCall.replay oracle law]

theorem headline (oracle : NFF_ProductCall.Oracle) (law : NFF_ProductCall.Law oracle)
    (a b : FIo_Native.fast_pairing.canonical.Q) :
    run oracle a b=FIo_Native.fast_pairing.canonical.Q.raw a b := by
  rw [replay oracle law,NFE_NFC_RawAssociation.source_eq]
  simp only [FIo_QRaw.canonical.Q.raw,AspisR1CanonicalQRawUnified.canonical.Q.raw,
    LPi_RawCallbacks.left,LPi_RawCallbacks.right,LPi_RawCallbacks.pp,
    LPi_RawCallbacks.fold_callback,FIo_QRaw.canonical.P,AspisR1CanonicalQRawUnified.canonical.P]

#print axioms headline
#print axioms replay
end AspisR1.NFF_LoggedRaw
