import R1Z.PV_L2_F6FlagLoop
set_option autoImplicit false
namespace R1Z.PV_L2_F6NullEntry
open Aeneas Aeneas.Std Result R1CertCheck R1Z.CertCheck R1Z.PV_L2_Record

def source (e : Slice U32) (n : Usize) (tag : Slice U32) (r ff t : Usize) : Result (U64 × U64 × U64) := do
  let i ← Slice.index_usize tag t
  let g ← lift (UScalar.cast .Usize i)
  let isf ← lift (UScalar.cast_fromBool .U64 (t = ff))
  let ip ← lift (UScalar.cast_fromBool .U64 (g < r))
  let i1 ← g % r
  let i2 ← i1 * n
  let i3 ← i2 + ff
  let i4 ← Slice.index_usize e i3
  let i5 ← lift (UScalar.cast .U64 i4)
  let ev ← i5 % P
  ok (isf,ip,ev)

def recorded (e : Slice U32) (n : Usize) (tag : Slice U32) (r ff t : Usize) : Recorded (U64 × U64 × U64) := do
  let i ← operation (.index 3 t.val) (Slice.index_usize tag t)
  let g := UScalar.cast .Usize i
  let isf ← operation (.guard 14 0 0 (t = ff)) (ok (UScalar.cast_fromBool .U64 (t = ff)))
  let ip ← operation (.guard 14 0 0 (g < r)) (ok (UScalar.cast_fromBool .U64 (g < r)))
  let i1 ← operation (.rem g.val r.val) (g % r)
  let i2 ← operation (.mul i1.val n.val) (i1 * n)
  let i3 ← operation (.add i2.val ff.val) (i2 + ff)
  let i4 ← operation (.index 1 i3.val) (Slice.index_usize e i3)
  let i5 := UScalar.cast .U64 i4
  let ev ← operation (.rem i5.val P.val) (i5 % P)
  PV_L2_Record.pure (isf,ip,ev)

theorem erases (e : Slice U32) (n : Usize) (tag : Slice U32) (r ff t : Usize) :
    (recorded e n tag r ff t).value = source e n tag r ff t := by
  simp only [recorded,source,operation_bind_value,operation_value,
    PV_L2_Record.pure_value,lift,bind_tc_ok]
#print axioms erases
end R1Z.PV_L2_F6NullEntry
