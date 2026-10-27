import RPz7_FIp_NativeDots
import RPt_FJf_U64Array
import RPt_FIo_RangeNext
import RPt_FIp_RangeNone
import RPt_FIo_LoopInvariant
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJi_Accumulations
open Aeneas Aeneas.Std Result ControlFlow
abbrev NE := FIo_Install.NE
abbrev Sums := Array U64 8#usize
abbrev Coefficients := Array U32 8#usize
/-- Exactly the installed eight coordinate updates after its SAME scalar and
coefficient decoder. No recurrence is evaluated here. -/
def accumulate (coefficient : Coefficients) (scalar : U32) (sums : Sums) : Result Sums := do
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

/-- One coordinate's actual checked-u64 arithmetic. -/
def lane (coefficient : Coefficients) (scalar : U32) (sums : Sums)
    (j : Usize) : Result Sums := do
  let c ← Array.index_usize coefficient j
  let a ← lift (core.convert.num.FromU64U32.from c)
  let b ← lift (core.convert.num.FromU64U32.from scalar)
  let product ← a*b
  let old ← Array.index_usize sums j
  let total ← old+product
  Array.update sums j total

def coordinate0 := fun (c : Coefficients) (a : U32) (s : Sums) => lane c a s 0#usize

def coordinate1 := fun (c : Coefficients) (a : U32) (s : Sums) => lane c a s 1#usize

def coordinate2 := fun (c : Coefficients) (a : U32) (s : Sums) => lane c a s 2#usize

def coordinate3 := fun (c : Coefficients) (a : U32) (s : Sums) => lane c a s 3#usize

def coordinate4 := fun (c : Coefficients) (a : U32) (s : Sums) => lane c a s 4#usize

def coordinate5 := fun (c : Coefficients) (a : U32) (s : Sums) => lane c a s 5#usize

def coordinate6 := fun (c : Coefficients) (a : U32) (s : Sums) => lane c a s 6#usize

def coordinate7 := fun (c : Coefficients) (a : U32) (s : Sums) => lane c a s 7#usize

/-- Source-order enumeration of all eight installed grouped-u64 updates. -/
theorem enumeration (c : Coefficients) (a : U32) (s : Sums) :
    accumulate c a s=(do
      let s1 ← coordinate0 c a s
      let s2 ← coordinate1 c a s1
      let s3 ← coordinate2 c a s2
      let s4 ← coordinate3 c a s3
      let s5 ← coordinate4 c a s4
      let s6 ← coordinate5 c a s5
      let s7 ← coordinate6 c a s6
      let s8 ← coordinate7 c a s7
      ok s8) := by
  simp only [accumulate,coordinate0,coordinate1,coordinate2,coordinate3,coordinate4,coordinate5,coordinate6,coordinate7,lane,bind_assoc_eq]
#print axioms enumeration
end AspisR1.FJi_Accumulations
end
