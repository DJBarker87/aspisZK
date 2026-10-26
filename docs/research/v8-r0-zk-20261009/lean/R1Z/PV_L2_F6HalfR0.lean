import R1Z.PV_L2_RecordRefinement
import R1Z.PV_L2_F6MM

set_option autoImplicit false
namespace R1Z.PV_L2_F6HalfR0
open Aeneas Aeneas.Std Result R1CertCheck R1Z.PV_L2_Record
local instance : Bind Recorded := ⟨@PV_L2_RecordCompact.bind⟩
def source (x01 x1 y0 y1 : U32) (p q : U64) : Result (U64) := do
  let i12 ← mm x01 y0
  let i13 ← i12 + P
  let i14 ← mm x1 y1
  let i15 ← i13 - i14
  let i16 ← 2#u64 * p
  let i17 ← i15 + i16
  let i18 ← i17 + P
  let i19 ← i18 - q
  let r0 ← i19 % P
  ok r0
def recorded (x01 x1 y0 y1 : U32) (p q : U64) : Recorded (U64) := do
  let i12 ← PV_L2_F6MM.recorded x01 y0
  let i13 ← operation (.add i12.val P.val) (i12 + P)
  let i14 ← PV_L2_F6MM.recorded x1 y1
  let i15 ← operation (.guard 34 i13.val i14.val true) (i13 - i14)
  let i16 ← operation (.mul (2#u64).val p.val) (2#u64 * p)
  let i17 ← operation (.add i15.val i16.val) (i15 + i16)
  let i18 ← operation (.add i17.val P.val) (i17 + P)
  let i19 ← operation (.guard 34 i18.val q.val true) (i18 - q)
  let r0 ← operation (.rem i19.val P.val) (i19 % P)
  PV_L2_Record.pure r0
theorem erases (x01 x1 y0 y1 : U32) (p q : U64) : (recorded x01 x1 y0 y1 p q).value = source x01 x1 y0 y1 p q := by
  simp only [recorded,source,PV_L2_RecordCompact.bind_value,
    PV_L2_F6MM.erases,PV_L2_RecordCompact.operation_bind_value,operation_value,
    PV_L2_Record.pure_value,lift,bind_tc_ok]
#print axioms erases
end R1Z.PV_L2_F6HalfR0
