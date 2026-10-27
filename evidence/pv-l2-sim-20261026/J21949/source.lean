import R1Z.PV_L2_RecordCompact
import R1Z.PV_L2_F6FlagLoop
import R1Z.PV_L2_F6Callers

set_option autoImplicit false
namespace R1Z.PV_L2_F6EntriesStep
open Aeneas Aeneas.Std Result R1CertCheck R1Z.CertCheck R1Z.PV_L2_Record
local instance : Bind Recorded := ⟨@PV_L2_RecordCompact.bind⟩
def step 
  (ej : Slice Std.U32) (es : Slice Std.U32) (epo : Slice Std.U32)
  (eco : Slice Std.U32) (idx : Slice Std.U32) (coef : Slice Std.U32)
  (m : Std.Usize) (lane : Slice Std.U32) (wl : Slice Std.U32)
  (z1 : Slice Std.U32) (s1 : Std.Usize) (z2 : Slice Std.U32) (s2 : Std.Usize)
  (n2 : Std.Usize) (g : Slice Std.U32) (sg : Std.Usize) (ng : Std.Usize)
  (out : Slice Std.U32) (zero : Slice Std.U32) (ok1 : Bool) (e : Usize) : Result (Bool × Usize) := do
  let i ← Slice.index_usize ej e
  let j ← lift (UScalar.cast .Usize i)
  let i1 ← Slice.index_usize es e
  let s ← lift (UScalar.cast .Usize i1)
  let i2 ← Slice.index_usize epo e
  let io ← lift (UScalar.cast .Usize i2)
  let i3 ← Slice.index_usize eco e
  let co ← lift (UScalar.cast .Usize i3)
  let lj ← Slice.index_usize lane j
  let i4 ← lift (UScalar.cast .Usize lj)
  let i5 ← Slice.index_usize wl i4
  let w1 ← lift (UScalar.cast .Usize i5)
  let b0 ← piv_ok idx io s lane lj
  let b1 ← kimg_ok z1 s1 w1 j idx io coef co s zero 0#usize 0#usize
  let b2 ← kimg_ok z2 s2 n2 j idx io coef co s zero 0#usize 0#usize
  let i6 ← e * ng
  let b3 ← kimg_ok g sg ng j idx io coef co s out i6 1#usize
  let e1 ← e + 1#usize
  ok ((((ok1 && b0) && b1) && b2) && b3,e1)
def recorded 
  (ej : Slice Std.U32) (es : Slice Std.U32) (epo : Slice Std.U32)
  (eco : Slice Std.U32) (idx : Slice Std.U32) (coef : Slice Std.U32)
  (m : Std.Usize) (lane : Slice Std.U32) (wl : Slice Std.U32)
  (z1 : Slice Std.U32) (s1 : Std.Usize) (z2 : Slice Std.U32) (s2 : Std.Usize)
  (n2 : Std.Usize) (g : Slice Std.U32) (sg : Std.Usize) (ng : Std.Usize)
  (out : Slice Std.U32) (zero : Slice Std.U32) (ok1 : Bool) (e : Usize) : Recorded (Bool × Usize) := do
  let i ← operation (.index 0 e.val) (Slice.index_usize ej e)
  let j := UScalar.cast .Usize i
  let i1 ← operation (.index 1 e.val) (Slice.index_usize es e)
  let s := UScalar.cast .Usize i1
  let i2 ← operation (.index 2 e.val) (Slice.index_usize epo e)
  let io := UScalar.cast .Usize i2
  let i3 ← operation (.index 3 e.val) (Slice.index_usize eco e)
  let co := UScalar.cast .Usize i3
  let lj ← operation (.index 7 j.val) (Slice.index_usize lane j)
  let i4 := UScalar.cast .Usize lj
  let i5 ← operation (.index 8 i4.val) (Slice.index_usize wl i4)
  let w1 := UScalar.cast .Usize i5
  let b0 ← PV_L2_F6Callers.piv idx io s lane lj
  let b1 ← PV_L2_F6Callers.image z1 s1 w1 j idx io coef co s zero 0#usize 0#usize
  let b2 ← PV_L2_F6Callers.image z2 s2 n2 j idx io coef co s zero 0#usize 0#usize
  let i6 ← operation (.mul e.val ng.val) (e * ng)
  let b3 ← PV_L2_F6Callers.image g sg ng j idx io coef co s out i6 1#usize
  let e1 ← operation (.add e.val (1#usize).val) (e + 1#usize)
  operation (.guard 24 0 0 ((((ok1 && b0) && b1) && b2) && b3)) (ok ((((ok1 && b0) && b1) && b2) && b3,e1))
theorem recorded_erases 
  (ej : Slice Std.U32) (es : Slice Std.U32) (epo : Slice Std.U32)
  (eco : Slice Std.U32) (idx : Slice Std.U32) (coef : Slice Std.U32)
  (m : Std.Usize) (lane : Slice Std.U32) (wl : Slice Std.U32)
  (z1 : Slice Std.U32) (s1 : Std.Usize) (z2 : Slice Std.U32) (s2 : Std.Usize)
  (n2 : Std.Usize) (g : Slice Std.U32) (sg : Std.Usize) (ng : Std.Usize)
  (out : Slice Std.U32) (zero : Slice Std.U32) (ok1 : Bool) (e : Usize) :
    (recorded ej es epo eco idx coef m lane wl z1 s1 z2 s2 n2 g sg ng out zero ok1 e).value = step ej es epo eco idx coef m lane wl z1 s1 z2 s2 n2 g sg ng out zero ok1 e := by
  simp only [recorded,step,PV_L2_RecordCompact.bind_value,
    PV_L2_F6Callers.piv_erases,PV_L2_F6Callers.image_erases,PV_L2_RecordCompact.operation_bind_value,
    operation_value,lift,bind_tc_ok]
theorem unroll 
  (ej : Slice Std.U32) (es : Slice Std.U32) (epo : Slice Std.U32)
  (eco : Slice Std.U32) (idx : Slice Std.U32) (coef : Slice Std.U32)
  (m : Std.Usize) (lane : Slice Std.U32) (wl : Slice Std.U32)
  (z1 : Slice Std.U32) (s1 : Std.Usize) (z2 : Slice Std.U32) (s2 : Std.Usize)
  (n2 : Std.Usize) (g : Slice Std.U32) (sg : Std.Usize) (ng : Std.Usize)
  (out : Slice Std.U32) (zero : Slice Std.U32) (ok1 : Bool) (e : Usize) :
    ents_ok_loop ej es epo eco idx coef m lane wl z1 s1 z2 s2 n2 g sg ng out zero ok1 e = if e<m then (do
      let (flag1,index1) ← step ej es epo eco idx coef m lane wl z1 s1 z2 s2 n2 g sg ng out zero ok1 e
      ents_ok_loop ej es epo eco idx coef m lane wl z1 s1 z2 s2 n2 g sg ng out zero flag1 index1) else ok ok1 := by
  rw [ents_ok_loop]
  split
  · simp only [step,bind_assoc_eq,bind_tc_ok]
  · rfl
theorem increment 
  (ej : Slice Std.U32) (es : Slice Std.U32) (epo : Slice Std.U32)
  (eco : Slice Std.U32) (idx : Slice Std.U32) (coef : Slice Std.U32)
  (m : Std.Usize) (lane : Slice Std.U32) (wl : Slice Std.U32)
  (z1 : Slice Std.U32) (s1 : Std.Usize) (z2 : Slice Std.U32) (s2 : Std.Usize)
  (n2 : Std.Usize) (g : Slice Std.U32) (sg : Std.Usize) (ng : Std.Usize)
  (out : Slice Std.U32) (zero : Slice Std.U32) (ok1 : Bool) (e : Usize) (after : Bool × Usize)
    (success : step ej es epo eco idx coef m lane wl z1 s1 z2 s2 n2 g sg ng out zero ok1 e = ok after) : after.2.val=e.val+1 := by
  unfold step at success
  obtain ⟨i,hi,success⟩ := bind_eq_ok success
  obtain ⟨j,hj,success⟩ := bind_eq_ok success
  obtain ⟨i1,hi1,success⟩ := bind_eq_ok success
  obtain ⟨s,hs,success⟩ := bind_eq_ok success
  obtain ⟨i2,hi2,success⟩ := bind_eq_ok success
  obtain ⟨io,hio,success⟩ := bind_eq_ok success
  obtain ⟨i3,hi3,success⟩ := bind_eq_ok success
  obtain ⟨co,hco,success⟩ := bind_eq_ok success
  obtain ⟨lj,hlj,success⟩ := bind_eq_ok success
  obtain ⟨i4,hi4,success⟩ := bind_eq_ok success
  obtain ⟨i5,hi5,success⟩ := bind_eq_ok success
  obtain ⟨w1,hw1,success⟩ := bind_eq_ok success
  obtain ⟨b0,hb0,success⟩ := bind_eq_ok success
  obtain ⟨b1,hb1,success⟩ := bind_eq_ok success
  obtain ⟨b2,hb2,success⟩ := bind_eq_ok success
  obtain ⟨i6,hi6,success⟩ := bind_eq_ok success
  obtain ⟨b3,hb3,success⟩ := bind_eq_ok success
  obtain ⟨e1,he1,success⟩ := bind_eq_ok success
  have he := ok_inj success
  rw [←he]
  simpa only [show (1#usize).val=1 from rfl] using add_ok he1
#print axioms recorded_erases
#print axioms unroll
#print axioms increment
end R1Z.PV_L2_F6EntriesStep
