import R1Z.PV_L2_RecordRefinement
import R1Z.PV_L2_F6MM

set_option autoImplicit false
namespace R1Z.PV_L2_F6HalfR1
open Aeneas Aeneas.Std Result R1CertCheck R1Z.PV_L2_Record
local instance : Bind Recorded := ⟨@PV_L2_RecordCompact.bind⟩
def source (x01 x1 y0 y1 : U32) (p q : U64) : Result (U64) := do
  let i20 ← mm x01 y1
  let i21 ← mm x1 y0
  let i22 ← i20 + i21
  let i23 ← i22 + p
  let i24 ← 2#u64 * q
  let i25 ← i23 + i24
  let r1 ← i25 % P
  ok r1
def recorded (x01 x1 y0 y1 : U32) (p q : U64) : Recorded (U64) := do
  let i20 ← PV_L2_F6MM.recorded x01 y1
  let i21 ← PV_L2_F6MM.recorded x1 y0
  let i22 ← operation (.add i20.val i21.val) (i20 + i21)
  let i23 ← operation (.add i22.val p.val) (i22 + p)
  let i24 ← operation (.mul (2#u64).val q.val) (2#u64 * q)
  let i25 ← operation (.add i23.val i24.val) (i23 + i24)
  let r1 ← operation (.rem i25.val P.val) (i25 % P)
  PV_L2_Record.pure r1
theorem erases (x01 x1 y0 y1 : U32) (p q : U64) : (recorded x01 x1 y0 y1 p q).value = source x01 x1 y0 y1 p q := by
  simp only [recorded,source,PV_L2_RecordCompact.bind_value,
    PV_L2_F6MM.erases,PV_L2_RecordCompact.operation_bind_value,operation_value,
    PV_L2_Record.pure_value,lift,bind_tc_ok]
#print axioms erases
end R1Z.PV_L2_F6HalfR1
