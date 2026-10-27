import R1Z.PV_L2_RecordRefinement
import R1Z.PV_L2_F6MM

set_option autoImplicit false
namespace R1Z.PV_L2_F6HalfR2
open Aeneas Aeneas.Std Result R1CertCheck R1Z.PV_L2_Record
local instance : Bind Recorded := ⟨@PV_L2_RecordCompact.bind⟩
def source (x01 x1 x2 x3 y0 y1 y2 y3 : U32) : Result (U64) := do
  let i26 ← mm x01 y2
  let i27 ← i26 + P
  let i28 ← mm x1 y3
  let i29 ← i27 - i28
  let i30 ← mm x2 y0
  let i31 ← i29 + i30
  let i32 ← i31 + P
  let i33 ← mm x3 y1
  let i34 ← i32 - i33
  let r2 ← i34 % P
  ok r2
def recorded (x01 x1 x2 x3 y0 y1 y2 y3 : U32) : Recorded (U64) := do
  let i26 ← PV_L2_F6MM.recorded x01 y2
  let i27 ← operation (.add i26.val P.val) (i26 + P)
  let i28 ← PV_L2_F6MM.recorded x1 y3
  let i29 ← operation (.guard 36 i27.val i28.val true) (i27 - i28)
  let i30 ← PV_L2_F6MM.recorded x2 y0
  let i31 ← operation (.add i29.val i30.val) (i29 + i30)
  let i32 ← operation (.add i31.val P.val) (i31 + P)
  let i33 ← PV_L2_F6MM.recorded x3 y1
  let i34 ← operation (.guard 36 i32.val i33.val true) (i32 - i33)
  let r2 ← operation (.rem i34.val P.val) (i34 % P)
  PV_L2_Record.pure r2
theorem erases (x01 x1 x2 x3 y0 y1 y2 y3 : U32) : (recorded x01 x1 x2 x3 y0 y1 y2 y3).value = source x01 x1 x2 x3 y0 y1 y2 y3 := by
  simp only [recorded,source,PV_L2_RecordCompact.bind_value,
    PV_L2_F6MM.erases,PV_L2_RecordCompact.operation_bind_value,operation_value,
    PV_L2_Record.pure_value,lift,bind_tc_ok]
#print axioms erases
end R1Z.PV_L2_F6HalfR2
