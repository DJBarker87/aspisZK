import R1Z.PV_L2_RecordRefinement
import R1Z.PV_L2_F6MM

set_option autoImplicit false
namespace R1Z.PV_L2_F6HalfR3
open Aeneas Aeneas.Std Result R1CertCheck R1Z.PV_L2_Record
local instance : Bind Recorded := ⟨@PV_L2_RecordCompact.bind⟩
def source (x01 x1 x2 x3 y0 y1 y2 y3 : U32) : Result (U64) := do
  let i35 ← mm x01 y3
  let i36 ← mm x1 y2
  let i37 ← i35 + i36
  let i38 ← mm x2 y1
  let i39 ← i37 + i38
  let i40 ← mm x3 y0
  let i41 ← i39 + i40
  let r3 ← i41 % P
  ok r3
def recorded (x01 x1 x2 x3 y0 y1 y2 y3 : U32) : Recorded (U64) := do
  let i35 ← PV_L2_F6MM.recorded x01 y3
  let i36 ← PV_L2_F6MM.recorded x1 y2
  let i37 ← operation (.add i35.val i36.val) (i35 + i36)
  let i38 ← PV_L2_F6MM.recorded x2 y1
  let i39 ← operation (.add i37.val i38.val) (i37 + i38)
  let i40 ← PV_L2_F6MM.recorded x3 y0
  let i41 ← operation (.add i39.val i40.val) (i39 + i40)
  let r3 ← operation (.rem i41.val P.val) (i41 % P)
  PV_L2_Record.pure r3
theorem erases (x01 x1 x2 x3 y0 y1 y2 y3 : U32) : (recorded x01 x1 x2 x3 y0 y1 y2 y3).value = source x01 x1 x2 x3 y0 y1 y2 y3 := by
  simp only [recorded,source,PV_L2_RecordCompact.bind_value,
    PV_L2_F6MM.erases,PV_L2_RecordCompact.operation_bind_value,operation_value,
    PV_L2_Record.pure_value,lift,bind_tc_ok]
#print axioms erases
end R1Z.PV_L2_F6HalfR3
