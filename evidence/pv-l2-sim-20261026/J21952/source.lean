import R1Z.PV_L2_RecordRefinement

set_option autoImplicit false
namespace R1Z.PV_L2_F6MM
open Aeneas Aeneas.Std Result R1CertCheck R1Z.PV_L2_Record
local instance : Bind Recorded := ⟨@PV_L2_RecordCompact.bind⟩
def source (x y : U32) : Result (U64) := do
  let i ← lift (UScalar.cast .U64 x)
  let i1 ← lift (UScalar.cast .U64 y)
  let i2 ← i * i1
  let out ← i2 % P
  ok out
def recorded (x y : U32) : Recorded (U64) := do
  let i := UScalar.cast .U64 x
  let i1 := UScalar.cast .U64 y
  let i2 ← operation (.mul i.val i1.val) (i * i1)
  let out ← operation (.rem i2.val P.val) (i2 % P)
  PV_L2_Record.pure out
theorem erases (x y : U32) : (recorded x y).value = R1CertCheck.mm x y := by
  simp only [recorded,R1CertCheck.mm,PV_L2_RecordCompact.bind_value,
    PV_L2_RecordCompact.operation_bind_value,operation_value,
    PV_L2_Record.pure_value,lift,bind_tc_ok]
  cases (UScalar.cast .U64 x) * (UScalar.cast .U64 y) <;>
    simp only [bind_tc_fail,bind_tc_div,bind_tc_ok]
  rename_i value
  cases value % P <;> rfl
#print axioms erases
end R1Z.PV_L2_F6MM
