import R1Z.PV_L2_BoolTrace
import R1Z.PV_L2_F6Callers
import R1Z.PV_L2_F6Echelon
import R1Z.PV_L2_F6Entries
import R1Z.PV_L2_F6Null
import R1Z.PV_L2_F6PermutationLeft
import R1Z.PV_L2_F6PermutationRight
set_option autoImplicit false
namespace R1Z.PV_L2_F6BCond
open Aeneas Aeneas.Std Result R1CertCheck R1Z.PV_L2_Record
local instance : Bind Recorded := ⟨@PV_L2_RecordCompact.bind⟩
def recorded (pb : Pub) (c : Cert) : Recorded Bool := do
  let n := UScalar.cast .Usize pb.bw
  let r := UScalar.cast .Usize c.r
  let k := UScalar.cast .Usize c.k
  let q := UScalar.cast .Usize pb.q
  let mg := UScalar.cast .Usize c.mg
  let rw := UScalar.cast .Usize pb.rw
  let i := alloc.vec.Vec.len c.lst
  let i1 := alloc.vec.Vec.len c.tag
  let i2 ← operation (.add r.val k.val) (r + k)
  let s := alloc.vec.Vec.deref c.u
  let s1 := alloc.vec.Vec.deref pb.rel
  let s2 := alloc.vec.Vec.deref c.e
  let e1 ← PV_L2_F6Callers.product s 0#usize s1 0#usize s2 0#usize r n q
  let s3 := alloc.vec.Vec.deref c.lst
  let s4 := alloc.vec.Vec.deref c.tag
  let e2 ← PV_L2_F6PermutationLeft.recorded s3 s4 n
  let s5 := alloc.vec.Vec.deref c.lst
  let s6 := alloc.vec.Vec.deref c.tag
  let e3 ← PV_L2_F6PermutationRight.recorded s5 s6 n
  let s7 := alloc.vec.Vec.deref c.e
  let s8 := alloc.vec.Vec.deref c.lst
  let e4 ← PV_L2_F6Echelon.recorded s7 n s8 r
  let s9 := alloc.vec.Vec.deref c.gej
  let s10 := alloc.vec.Vec.deref c.ges
  let s11 := alloc.vec.Vec.deref c.gepo
  let s12 := alloc.vec.Vec.deref c.geco
  let s13 := alloc.vec.Vec.deref c.gpidx
  let s14 := alloc.vec.Vec.deref c.gcoef
  let s15 := alloc.vec.Vec.deref pb.glane
  let s16 := alloc.vec.Vec.deref pb.gwl
  let s17 := alloc.vec.Vec.deref pb.gown
  let i3 := UScalar.cast .Usize pb.gw
  let s18 := alloc.vec.Vec.deref pb.ground
  let s19 := alloc.vec.Vec.deref pb.gbat
  let s20 := alloc.vec.Vec.deref c.beta
  let s21 := Array.to_slice (Array.make 1#usize [ 0#u32 ])
  let g1 ← PV_L2_F6Entries.recorded s9 s10 s11 s12 s13 s14 mg s15 s16 s17 i3 s18 rw rw s19 n n s20 s21
  let s22 := alloc.vec.Vec.deref c.nm
  let s23 := alloc.vec.Vec.deref c.e
  let s24 := alloc.vec.Vec.deref c.lst
  let s25 := alloc.vec.Vec.deref c.tag
  let g2 ← PV_L2_F6Null.recorded s22 s23 n s24 s25 r k
  let s26 := alloc.vec.Vec.deref c.yg
  let s27 := alloc.vec.Vec.deref c.beta
  let s28 := alloc.vec.Vec.deref c.nm
  let g3 ← PV_L2_F6Callers.product s26 0#usize s27 0#usize s28 0#usize k n mg
  PV_L2_BoolTrace.conjunction 51 0 [(i = n),(i1 = n),(i2 = n),(e1),(e2),(e3),(e4),(g1),(g2),(g3)]
theorem erases (pb : Pub) (c : Cert) : (recorded pb c).value = check_bcond pb c := by
  simp only [recorded,check_bcond,PV_L2_RecordCompact.bind_value,
    PV_L2_F6Callers.product_erases,PV_L2_F6PermutationLeft.erases,PV_L2_F6PermutationRight.erases,PV_L2_F6Echelon.erases,PV_L2_F6Entries.erases,PV_L2_F6Null.erases,PV_L2_BoolTrace.value,
    operation_value,lift,bind_tc_ok,List.foldr_cons,List.foldr_nil,
    Bool.and_true,Bool.and_assoc]
#print axioms erases
end R1Z.PV_L2_F6BCond
