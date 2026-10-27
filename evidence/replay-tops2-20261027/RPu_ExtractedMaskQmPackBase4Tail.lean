import RPu_ExtractedMaskQmPackBase4SourceArithmetic
import RPu_ExtractedMaskQmPackBase4CheckedU64

/-! The arithmetic tail of the exact current generated `qm31_pack_base4`
declaration, after the four stored QM31 values and widened field modulus have
been read. This isolates the operation sequence from the Slice/array prefix. -/
set_option autoImplicit false
namespace AspisR1.ExtractedMaskQmPackBase4Tail

open Aeneas.Std Result
open AspisR1.ExtractedMaskQmPackBase4Arithmetic
open AspisR1.ExtractedMaskQmPackBase4SourceArithmetic
open AspisR1.ExtractedMaskQmPackBase4CheckedU64

abbrev CurrentQM := AspisR1.ExtractedMaskQM31Exact.CurrentQM
abbrev CurrentCanonicalQM := AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM

/-- Literal post-read tail from the generated function, retaining its source
operation order and its actual reducer and constructor calls. -/
def run (v : Fin 4 → CurrentQM) : Result CurrentQM := do
  let v0 := v 0
  let v1 := v 1
  let v2 := v 2
  let v3 := v 3
  let p := sourceP64
  let i2 ← packLimbCall v0.c0.a
  let i3 ← packLimbCall v1.c0.b
  let i4 ← UScalar.sub p i3
  let i5 ← UScalar.add i2 i4
  let i6 ← packLimbCall v2.c1.a
  let i7 ← UScalar.mul (2#u64) i6
  let i8 ← UScalar.add i5 i7
  let i9 ← packLimbCall v2.c1.b
  let i10 ← UScalar.sub p i9
  let i11 ← UScalar.add i8 i10
  let i12 ← packLimbCall v3.c1.a
  let i13 ← UScalar.sub p i12
  let i14 ← UScalar.add i11 i13
  let i15 ← UScalar.mul (2#u64) p
  let i16 ← packLimbCall v3.c1.b
  let i17 ← UScalar.mul (2#u64) i16
  let i18 ← UScalar.sub i15 i17
  let c0a ← UScalar.add i14 i18
  let i19 ← packLimbCall v0.c0.b
  let i20 ← packLimbCall v1.c0.a
  let i21 ← UScalar.add i19 i20
  let i22 ← UScalar.add i21 i6
  let i23 ← UScalar.mul (2#u64) i9
  let i24 ← UScalar.add i22 i23
  let i25 ← UScalar.mul (2#u64) i12
  let i26 ← UScalar.add i24 i25
  let i27 ← UScalar.sub p i16
  let c0b ← UScalar.add i26 i27
  let i28 ← packLimbCall v0.c1.a
  let i29 ← packLimbCall v1.c1.b
  let i30 ← UScalar.sub p i29
  let i31 ← UScalar.add i28 i30
  let i32 ← packLimbCall v2.c0.a
  let i33 ← UScalar.add i31 i32
  let i34 ← packLimbCall v3.c0.b
  let i35 ← UScalar.sub p i34
  let c1a ← UScalar.add i33 i35
  let i36 ← packLimbCall v0.c1.b
  let i37 ← packLimbCall v1.c1.a
  let i38 ← UScalar.add i36 i37
  let i39 ← packLimbCall v2.c0.b
  let i40 ← UScalar.add i38 i39
  let i41 ← packLimbCall v3.c0.a
  let c1b ← UScalar.add i40 i41
  let m ← AspisR1SelectedMaskProbe.field.M31.reduce_u64 c0a
  let m1 ← AspisR1SelectedMaskProbe.field.M31.reduce_u64 c0b
  let c ← AspisR1SelectedMaskProbe.field.CM31.new m m1
  let m2 ← AspisR1SelectedMaskProbe.field.M31.reduce_u64 c1a
  let m3 ← AspisR1SelectedMaskProbe.field.M31.reduce_u64 c1b
  let c1 ← AspisR1SelectedMaskProbe.field.CM31.new m2 m3
  ok ⟨c, c1⟩

end AspisR1.ExtractedMaskQmPackBase4Tail
