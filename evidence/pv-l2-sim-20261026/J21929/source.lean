import R1Z.PV_L2_F6NullEntry
import R1Z.PV_L2_F6NullWant
import R1Z.PV_L2_RecordBind
/-! Exceptional long null-vector step: named Entry and Want boundaries
replace the J21917 monolithic normalization. No cap increase. -/
set_option autoImplicit false
namespace R1Z.PV_L2_F6NullRowStep
open Aeneas Aeneas.Std Result R1CertCheck R1Z.CertCheck R1Z.PV_L2_Record

def step (nm e : Slice U32) (n : Usize) (tag : Slice U32) (r f ff : Usize) (ok1 : Bool) (t : Usize) : Result (Bool × Usize) := do
  let (isf,ip,ev) ← PV_L2_F6NullEntry.source e n tag r ff t
  let want ← PV_L2_F6NullWant.source isf ip ev
  let i9 ← f * n
  let i10 ← i9 + t
  let i11 ← Slice.index_usize nm i10
  let i12 ← lift (UScalar.cast .U64 i11)
  let t1 ← t + 1#usize
  ok (ok1 && (i12 = want),t1)

def recorded (nm e : Slice U32) (n : Usize) (tag : Slice U32) (r f ff : Usize) (ok1 : Bool) (t : Usize) : Recorded (Bool × Usize) := do
  let (isf,ip,ev) ← PV_L2_F6NullEntry.recorded e n tag r ff t
  let want ← PV_L2_F6NullWant.recorded isf ip ev
  let i9 ← operation (.mul f.val n.val) (f * n)
  let i10 ← operation (.add i9.val t.val) (i9 + t)
  let i11 ← operation (.index 0 i10.val) (Slice.index_usize nm i10)
  let i12 := UScalar.cast .U64 i11
  let t1 ← operation (.add t.val (1#usize).val) (t + 1#usize)
  operation (.guard 14 0 0 (i12 = want)) (ok (ok1 && (i12 = want),t1))

attribute [local irreducible] PV_L2_F6NullEntry.source PV_L2_F6NullWant.source
  PV_L2_F6NullEntry.recorded PV_L2_F6NullWant.recorded

theorem recorded_erases (nm e : Slice U32) (n : Usize) (tag : Slice U32) (r f ff : Usize) (ok1 : Bool) (t : Usize) :
    (recorded nm e n tag r f ff ok1 t).value = step nm e n tag r f ff ok1 t := by
  unfold recorded step
  rw [PV_L2_RecordBind.erase_bind,PV_L2_F6NullEntry.erases]
  congr 1
  funext entry
  rcases entry with ⟨isf,ip,ev⟩
  dsimp only
  rw [PV_L2_RecordBind.erase_bind,PV_L2_F6NullWant.erases]
  congr 1
  funext want
  simp only [operation_bind_value,operation_value,lift,bind_tc_ok]

#print axioms recorded_erases

theorem unroll (nm e : Slice U32) (n : Usize) (tag : Slice U32) (r f ff : Usize) (ok1 : Bool) (t : Usize) :
    nvec_row_ok_loop nm e n tag r f ff ok1 t =
      if t<n then (do
        let (flag1,index1) ← step nm e n tag r f ff ok1 t
        nvec_row_ok_loop nm e n tag r f ff flag1 index1) else ok ok1 := by
  rw [nvec_row_ok_loop]
  split
  · simp only [step,PV_L2_F6NullEntry.source,PV_L2_F6NullWant.source,bind_assoc_eq,bind_tc_ok]
  · rfl

theorem increment (nm e : Slice U32) (n : Usize) (tag : Slice U32) (r f ff : Usize) (ok1 : Bool) (t : Usize) (after : Bool × Usize)
    (success : step nm e n tag r f ff ok1 t = ok after) : after.2.val=t.val+1 := by
  unfold step at success
  obtain ⟨entry,he,success⟩ := bind_eq_ok success
  rcases entry with ⟨isf,ip,ev⟩
  obtain ⟨want,hw,success⟩ := bind_eq_ok success
  obtain ⟨i9,hi9,success⟩ := bind_eq_ok success
  obtain ⟨i10,hi10,success⟩ := bind_eq_ok success
  obtain ⟨i11,hi11,success⟩ := bind_eq_ok success
  obtain ⟨i12,hi12,success⟩ := bind_eq_ok success
  obtain ⟨t1,ht1,success⟩ := bind_eq_ok success
  have heq := ok_inj success
  rw [←heq]
  simpa only [show (1#usize).val=1 from rfl] using add_ok ht1
#print axioms recorded_erases
#print axioms unroll
#print axioms increment
end R1Z.PV_L2_F6NullRowStep
