import RPu_FJe_Component0
import RPu_FJe_Component1
import RPu_FJe_Component2
import RPu_FJe_Component3
import RPu_FJe_PackedTableRead
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJe_PackedRawAfter
open Aeneas Aeneas.Std Result FIq_Native
open FJb_TailCell (cell)
open FJe_PackedTableRead
abbrev Table := Array (Array U64 4#usize) 4#usize
def words (table : Table) (r j : Fin 4) : U64 := cell (cell table r) j
/-- The exact original finite arithmetic suffix after table construction. -/
def source (table : Table) (bound : U64) : Result (Array U64 4#usize) := do
  let a1 ← Array.index_usize table 0#usize
  let i ← Array.index_usize a1 0#usize
  let i1 ← 5#u64 * bound
  let i2 ← i + i1
  let a2 ← Array.index_usize table 1#usize
  let i3 ← Array.index_usize a2 1#usize
  let i4 ← i2 - i3
  let a3 ← Array.index_usize table 2#usize
  let i5 ← Array.index_usize a3 2#usize
  let i6 ← 2#u64 * i5
  let i7 ← i4 + i6
  let i8 ← Array.index_usize a3 3#usize
  let i9 ← i7 - i8
  let a4 ← Array.index_usize table 3#usize
  let i10 ← Array.index_usize a4 2#usize
  let i11 ← i9 - i10
  let i12 ← Array.index_usize a4 3#usize
  let i13 ← 2#u64 * i12
  let i14 ← i11 - i13
  let i15 ← Array.index_usize a1 1#usize
  let i16 ← Array.index_usize a2 0#usize
  let i17 ← i15 + i16
  let i18 ← Array.index_usize a3 2#usize
  let i19 ← i17 + i18
  let i20 ← Array.index_usize a3 3#usize
  let i21 ← 2#u64 * i20
  let i22 ← i19 + i21
  let i23 ← Array.index_usize a4 2#usize
  let i24 ← 2#u64 * i23
  let i25 ← i22 + i24
  let i26 ← i25 + bound
  let i27 ← Array.index_usize a4 3#usize
  let i28 ← i26 - i27
  let i29 ← Array.index_usize a1 2#usize
  let i30 ← 2#u64 * bound
  let i31 ← i29 + i30
  let i32 ← Array.index_usize a2 3#usize
  let i33 ← i31 - i32
  let i34 ← Array.index_usize a3 0#usize
  let i35 ← i33 + i34
  let i36 ← Array.index_usize a4 1#usize
  let i37 ← i35 - i36
  let i38 ← Array.index_usize a1 3#usize
  let i39 ← Array.index_usize a2 2#usize
  let i40 ← i38 + i39
  let i41 ← Array.index_usize a3 1#usize
  let i42 ← i40 + i41
  let i43 ← Array.index_usize a4 0#usize
  let i44 ← i42 + i43
  ok (Array.make 4#usize [ i14, i28, i37, i44 ])


def components (table : Table) (bound : U64) : Result (Array U64 4#usize) := do
  let x0 ← FJe_Component0.component0Ops bound (words table)
  let x1 ← FJe_Component1.component1Ops bound (words table)
  let x2 ← FJe_Component2.component2Ops bound (words table)
  let x3 ← FJe_Component3.component3Ops (words table)
  ok (Array.make 4#usize [x0,x1,x2,x3])

theorem factor (table : Table) (bound : U64) : source table bound=components table bound := by
  simp only [source,components,FJe_Component0.component0Ops,FJe_Component1.component1Ops,
    FJe_Component2.component2Ops,FJe_Component3.component3Ops,words,
    read0,read1,read2,read3,bind_tc_ok,bind_assoc_eq]
#print axioms factor
end AspisR1.FJe_PackedRawAfter
end
