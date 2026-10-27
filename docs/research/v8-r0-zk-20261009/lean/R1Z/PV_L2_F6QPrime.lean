import R1Z.PV_L2_BoolTrace
import R1Z.PV_L2_F6Callers
import R1Z.PV_L2_F6Entries
set_option autoImplicit false
namespace R1Z.PV_L2_F6QPrime
open Aeneas Aeneas.Std Result R1CertCheck R1Z.PV_L2_Record
local instance : Bind Recorded := ⟨@PV_L2_RecordCompact.bind⟩
def recorded (pb : Pub) (c : Cert) : Recorded Bool := do
  let rw := UScalar.cast .Usize pb.rw
  let m := UScalar.cast .Usize c.m
  let s := alloc.vec.Vec.deref c.ej
  let s1 := alloc.vec.Vec.deref c.es
  let s2 := alloc.vec.Vec.deref c.epo
  let s3 := alloc.vec.Vec.deref c.eco
  let s4 := alloc.vec.Vec.deref c.pidx
  let s5 := alloc.vec.Vec.deref c.coef
  let s6 := alloc.vec.Vec.deref pb.lane
  let s7 := alloc.vec.Vec.deref pb.wl
  let s8 := alloc.vec.Vec.deref pb.own
  let i := UScalar.cast .Usize pb.os
  let s9 := alloc.vec.Vec.deref pb.round
  let s10 := alloc.vec.Vec.deref pb.round
  let s11 := alloc.vec.Vec.deref c.rho
  let s12 := Array.to_slice (Array.make 1#usize [ 0#u32 ])
  let a ← PV_L2_F6Entries.recorded s s1 s2 s3 s4 s5 m s6 s7 s8 i s9 rw 0#usize s10 rw rw s11 s12
  let s13 := alloc.vec.Vec.deref c.y
  let s14 := alloc.vec.Vec.deref c.rho
  let s15 := alloc.vec.Vec.deref pb.tq
  let b ← PV_L2_F6Callers.product s13 0#usize s14 0#usize s15 0#usize rw rw m
  PV_L2_BoolTrace.conjunction 50 0 [(a),(b)]
theorem erases (pb : Pub) (c : Cert) : (recorded pb c).value = check_qprime pb c := by
  simp only [recorded,check_qprime,PV_L2_RecordCompact.bind_value,
    PV_L2_F6Entries.erases,PV_L2_F6Callers.product_erases,PV_L2_BoolTrace.value,
    operation_value,lift,bind_tc_ok,List.foldr_cons,List.foldr_nil,
    Bool.and_true,Bool.and_assoc]
#print axioms erases
end R1Z.PV_L2_F6QPrime
