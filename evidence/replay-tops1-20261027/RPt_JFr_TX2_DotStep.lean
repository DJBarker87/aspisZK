import RPt_JFr_TX2_ScalarRead
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFr_TX2_DotStep
open Aeneas Aeneas.Std Result ControlFlow
abbrev NE := FIo_Install.NE

/-- The unchanged eight-limb accumulation suffix of the native term body. -/
def update (g : Array NE 29#usize) (term : Usize) (scalar : U32)
    (sums : Array U64 8#usize) : Result (Array U64 8#usize) := do
  let we ← Array.index_usize g term
  let coefficient ← FIo_Native.aspis_core.field.wide_exact.WideExact.to_limbs we
  let i5 ← Array.index_usize coefficient 0#usize
  let i6 ← lift (core.convert.num.FromU64U32.from i5)
  let i7 ← lift (core.convert.num.FromU64U32.from scalar)
  let i8 ← i6 * i7
  let i9 ← Array.index_usize sums 0#usize
  let i10 ← i9 + i8
  let sums1 ← Array.update sums 0#usize i10
  let i11 ← Array.index_usize coefficient 1#usize
  let i12 ← lift (core.convert.num.FromU64U32.from i11)
  let i13 ← lift (core.convert.num.FromU64U32.from scalar)
  let i14 ← i12 * i13
  let i15 ← Array.index_usize sums1 1#usize
  let i16 ← i15 + i14
  let sums2 ← Array.update sums1 1#usize i16
  let i17 ← Array.index_usize coefficient 2#usize
  let i18 ← lift (core.convert.num.FromU64U32.from i17)
  let i19 ← lift (core.convert.num.FromU64U32.from scalar)
  let i20 ← i18 * i19
  let i21 ← Array.index_usize sums2 2#usize
  let i22 ← i21 + i20
  let sums3 ← Array.update sums2 2#usize i22
  let i23 ← Array.index_usize coefficient 3#usize
  let i24 ← lift (core.convert.num.FromU64U32.from i23)
  let i25 ← lift (core.convert.num.FromU64U32.from scalar)
  let i26 ← i24 * i25
  let i27 ← Array.index_usize sums3 3#usize
  let i28 ← i27 + i26
  let sums4 ← Array.update sums3 3#usize i28
  let i29 ← Array.index_usize coefficient 4#usize
  let i30 ← lift (core.convert.num.FromU64U32.from i29)
  let i31 ← lift (core.convert.num.FromU64U32.from scalar)
  let i32 ← i30 * i31
  let i33 ← Array.index_usize sums4 4#usize
  let i34 ← i33 + i32
  let sums5 ← Array.update sums4 4#usize i34
  let i35 ← Array.index_usize coefficient 5#usize
  let i36 ← lift (core.convert.num.FromU64U32.from i35)
  let i37 ← lift (core.convert.num.FromU64U32.from scalar)
  let i38 ← i36 * i37
  let i39 ← Array.index_usize sums5 5#usize
  let i40 ← i39 + i38
  let sums6 ← Array.update sums5 5#usize i40
  let i41 ← Array.index_usize coefficient 6#usize
  let i42 ← lift (core.convert.num.FromU64U32.from i41)
  let i43 ← lift (core.convert.num.FromU64U32.from scalar)
  let i44 ← i42 * i43
  let i45 ← Array.index_usize sums6 6#usize
  let i46 ← i45 + i44
  let sums7 ← Array.update sums6 6#usize i46
  let i47 ← Array.index_usize coefficient 7#usize
  let i48 ← lift (core.convert.num.FromU64U32.from i47)
  let i49 ← lift (core.convert.num.FromU64U32.from scalar)
  let i50 ← i48 * i49
  let i51 ← Array.index_usize sums7 7#usize
  let i52 ← i51 + i50
  let sums8 ← Array.update sums7 7#usize i52
  ok sums8

def step (q : Array U8 608#usize) (g : Array NE 29#usize) (slot : Usize)
    (iter : core.ops.range.Range Usize) (sums : Array U64 8#usize) :
    Result (ControlFlow (core.ops.range.Range Usize × Array U64 8#usize) (Array U64 8#usize)) := do
  let (o,next) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done sums)
  | some term => do
    let scalar ← JFr_TX2_ScalarRead.read q slot term
    let out ← update g term scalar sums
    ok (cont (next,out))

/-- Factoring only monadic association exposes the computed scalar-read
facts at their actual native call site. No loop-success premise is added. -/
theorem body (q : Array U8 608#usize) (g : Array NE 29#usize) (slot : Usize)
    (iter : core.ops.range.Range Usize) (sums : Array U64 8#usize) :
    FIp_NativeDots.fast_dots.four_dots_one_loop0_loop0.body q g slot iter sums=
      step q g slot iter sums := by
  simp only [FIp_NativeDots.fast_dots.four_dots_one_loop0_loop0.body,
    step,JFr_TX2_ScalarRead.read,update,bind_assoc_eq,bind_tc_ok]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  rintro ⟨o,next⟩ h
  cases o <;> simp only [Aeneas.Std.uncurry,bind_assoc_eq,bind_tc_ok]

#print axioms body
end AspisR1.JFr_TX2_DotStep
end
