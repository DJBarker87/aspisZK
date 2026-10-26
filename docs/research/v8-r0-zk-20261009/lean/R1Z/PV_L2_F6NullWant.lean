import R1Z.PV_L2_F6FlagLoop
set_option autoImplicit false
namespace R1Z.PV_L2_F6NullWant
open Aeneas Aeneas.Std Result R1CertCheck R1Z.CertCheck R1Z.PV_L2_Record

def source (isf ip ev : U64) : Result U64 := do
  let i6 ← isf + P
  let i7 ← ip * ev
  let i8 ← i6 - i7
  let want ← i8 % P
  ok want

def recorded (isf ip ev : U64) : Recorded U64 := do
  let i6 ← operation (.add isf.val P.val) (isf + P)
  let i7 ← operation (.mul ip.val ev.val) (ip * ev)
  let i8 ← operation (.guard 14 i6.val i7.val true) (i6 - i7)
  let want ← operation (.rem i8.val P.val) (i8 % P)
  PV_L2_Record.pure want

theorem erases (isf ip ev : U64) :
    (recorded isf ip ev).value = source isf ip ev := by
  simp only [recorded,source,operation_bind_value,operation_value,
    PV_L2_Record.pure_value,lift,bind_tc_ok]
#print axioms erases
end R1Z.PV_L2_F6NullWant
