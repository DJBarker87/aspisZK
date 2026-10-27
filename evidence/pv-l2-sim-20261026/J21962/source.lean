import R1Z.PV_L2_RecordRefinement
import R1Z.PV_L2_F6MM

set_option autoImplicit false
namespace R1Z.PV_L2_F6HalfPQ
open Aeneas Aeneas.Std Result R1CertCheck R1Z.PV_L2_Record
local instance : Bind Recorded := ⟨@PV_L2_RecordCompact.bind⟩
def source (x2 x3 y2 y3 : U32) : Result (U64 × U64) := do
  let i5 ← mm x2 y2
  let i6 ← i5 + P
  let i7 ← mm x3 y3
  let i8 ← i6 - i7
  let p ← i8 % P
  let i9 ← mm x2 y3
  let i10 ← mm x3 y2
  let i11 ← i9 + i10
  let q ← i11 % P
  ok (p,q)
def recorded (x2 x3 y2 y3 : U32) : Recorded (U64 × U64) := do
  let i5 ← PV_L2_F6MM.recorded x2 y2
  let i6 ← operation (.add i5.val P.val) (i5 + P)
  let i7 ← PV_L2_F6MM.recorded x3 y3
  let i8 ← operation (.guard 33 i6.val i7.val true) (i6 - i7)
  let p ← operation (.rem i8.val P.val) (i8 % P)
  let i9 ← PV_L2_F6MM.recorded x2 y3
  let i10 ← PV_L2_F6MM.recorded x3 y2
  let i11 ← operation (.add i9.val i10.val) (i9 + i10)
  let q ← operation (.rem i11.val P.val) (i11 % P)
  PV_L2_Record.pure (p,q)
theorem erases (x2 x3 y2 y3 : U32) : (recorded x2 x3 y2 y3).value = source x2 x3 y2 y3 := by
  simp only [recorded,source,PV_L2_RecordCompact.bind_value,
    PV_L2_F6MM.erases,PV_L2_RecordCompact.operation_bind_value,operation_value,
    PV_L2_Record.pure_value,lift,bind_tc_ok]
#print axioms erases
end R1Z.PV_L2_F6HalfPQ
