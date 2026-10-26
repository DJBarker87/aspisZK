import R1Z.PV_L2_RecordCompact
set_option autoImplicit false
namespace R1Z.PV_L2_F6NullFinish
open Aeneas Aeneas.Std Result R1CertCheck R1Z.CertCheck R1Z.PV_L2_Record

def source (nm : Slice U32) (n f : Usize) (ok1 : Bool) (t : Usize) (want : U64) : Result (Bool × Usize) := do
  let i9 ← f * n
  let i10 ← i9 + t
  let i11 ← Slice.index_usize nm i10
  let i12 ← lift (UScalar.cast .U64 i11)
  let t1 ← t + 1#usize
  ok (ok1 && (i12 = want),t1)

def recorded (nm : Slice U32) (n f : Usize) (ok1 : Bool) (t : Usize) (want : U64) : Recorded (Bool × Usize) := do
  let i9 ← operation (.mul f.val n.val) (f * n)
  let i10 ← operation (.add i9.val t.val) (i9 + t)
  let i11 ← operation (.index 0 i10.val) (Slice.index_usize nm i10)
  let i12 := UScalar.cast .U64 i11
  let t1 ← operation (.add t.val (1#usize).val) (t + 1#usize)
  operation (.guard 14 0 0 (i12 = want)) (ok (ok1 && (i12 = want),t1))

theorem erases (nm : Slice U32) (n f : Usize) (ok1 : Bool) (t : Usize) (want : U64) :
    (recorded nm n f ok1 t want).value = source nm n f ok1 t want := by
  simp only [recorded,source,operation_bind_value,operation_value,lift,bind_tc_ok]
#print axioms erases
end R1Z.PV_L2_F6NullFinish
