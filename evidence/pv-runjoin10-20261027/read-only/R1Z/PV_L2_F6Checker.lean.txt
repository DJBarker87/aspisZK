import R1Z.PV_L2_BoolTrace
import R1Z.PV_L2_F6BCond
import R1Z.PV_L2_F6Half
import R1Z.PV_L2_F6Lifts
import R1Z.PV_L2_F6QPrime
set_option autoImplicit false
namespace R1Z.PV_L2_F6Checker
open Aeneas Aeneas.Std Result R1CertCheck R1Z.PV_L2_Record
local instance : Bind Recorded := ⟨@PV_L2_RecordCompact.bind⟩
def recorded (pb : Pub) (c : Cert) : Recorded Bool := do
  let s := alloc.vec.Vec.deref pb.a9
  let s1 := alloc.vec.Vec.deref c.hinv
  let h ← PV_L2_F6Half.recorded s s1
  let s2 := alloc.vec.Vec.deref pb.lo
  let s3 := alloc.vec.Vec.deref c.lu
  let s4 := alloc.vec.Vec.deref c.lid
  let s5 := alloc.vec.Vec.deref pb.lw
  let s6 := alloc.vec.Vec.deref pb.loff
  let i := UScalar.cast .Usize pb.nl
  let li ← PV_L2_F6Lifts.recorded s2 s3 s4 s5 s6 i
  let qp ← PV_L2_F6QPrime.recorded pb c
  let bc ← PV_L2_F6BCond.recorded pb c
  PV_L2_BoolTrace.conjunction 52 0 [(h),(pb.nq <= 22#u32),(li),(qp),(bc)]
theorem erases (pb : Pub) (c : Cert) : (recorded pb c).value = check pb c := by
  simp only [recorded,check,PV_L2_RecordCompact.bind_value,
    PV_L2_F6Half.erases,PV_L2_F6Lifts.erases,PV_L2_F6QPrime.erases,PV_L2_F6BCond.erases,PV_L2_BoolTrace.value,
    operation_value,lift,bind_tc_ok,List.foldr_cons,List.foldr_nil,
    Bool.and_true,Bool.and_assoc]
#print axioms erases
end R1Z.PV_L2_F6Checker
