import AspisR1ProducerRelease47.SparseScan50
import R1Z.PV_L2_RecordCompact
set_option autoImplicit false
namespace R1Z.PV_L2_F5SparsePred
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47 R1Z.PV_L2_Record
local instance : Bind Recorded := ⟨@PV_L2_RecordCompact.bind⟩

def test (site : Nat) (x y : U32) : Recorded Bool :=
  operation (.guard site x.val y.val (x=y)) (ok (x=y))

def one (x : field.QM31) : Recorded Bool := do
  let a ← test 100 x.c0.a 1#u32
  if a then
    let b ← test 101 x.c0.b 0#u32
    if b then
      let c ← test 102 x.c1.a 0#u32
      if c then test 103 x.c1.b 0#u32 else PV_L2_Record.pure false
    else PV_L2_Record.pure false
  else PV_L2_Record.pure false

def boolean (x : field.QM31) : Recorded Bool := do
  let b ← test 104 x.c0.b 0#u32
  if b then
    let c ← test 105 x.c1.a 0#u32
    if c then
      let d ← test 106 x.c1.b 0#u32
      if d then
        let a ← test 107 x.c0.a 0#u32
        if a then PV_L2_Record.pure true else test 108 x.c0.a 1#u32
      else PV_L2_Record.pure false
    else PV_L2_Record.pure false
  else PV_L2_Record.pure false

theorem one_erases (x : field.QM31) : (one x).value = sparse_scan50.one x := by
  by_cases ha : x.c0.a=1#u32 <;> by_cases hb : x.c0.b=0#u32 <;>
    by_cases hc : x.c1.a=0#u32 <;> by_cases hd : x.c1.b=0#u32 <;>
    simp only [one,test,sparse_scan50.one,PV_L2_RecordCompact.bind_value,
      operation_value,PV_L2_Record.pure_value,bind_tc_ok,ha,hb,hc,hd,
      decide_true,decide_false,Bool.false_eq_true,if_true,if_false]

theorem boolean_erases (x : field.QM31) :
    (boolean x).value = sparse_scan50.boolean x := by
  by_cases ha0 : x.c0.a=0#u32 <;> by_cases ha1 : x.c0.a=1#u32 <;>
    by_cases hb : x.c0.b=0#u32 <;> by_cases hc : x.c1.a=0#u32 <;>
    by_cases hd : x.c1.b=0#u32 <;>
    simp only [boolean,test,sparse_scan50.boolean,PV_L2_RecordCompact.bind_value,
      operation_value,PV_L2_Record.pure_value,bind_tc_ok,ha0,ha1,hb,hc,hd,
      decide_true,decide_false,Bool.false_eq_true,if_true,if_false]

  all_goals rfl

#print axioms one_erases
#print axioms boolean_erases
end R1Z.PV_L2_F5SparsePred
