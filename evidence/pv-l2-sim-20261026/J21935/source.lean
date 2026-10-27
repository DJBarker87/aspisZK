import R1Z.PV_L2_F6NullEntry
import R1Z.PV_L2_F6NullWant
import R1Z.PV_L2_RecordRefinement
import R1Z.PV_L2_F6NullFinish
/-! Exceptional long null-vector step: named Entry and Want boundaries
replace the J21917 monolithic normalization. No cap increase. -/
set_option autoImplicit false
namespace R1Z.PV_L2_F6NullRowStep
open Aeneas Aeneas.Std Result R1CertCheck R1Z.CertCheck R1Z.PV_L2_Record

local instance : Bind Recorded := ⟨@PV_L2_RecordCompact.bind⟩

def step (nm e : Slice U32) (n : Usize) (tag : Slice U32) (r f ff : Usize) (ok1 : Bool) (t : Usize) : Result (Bool × Usize) := do
  let (isf,ip,ev) ← PV_L2_F6NullEntry.source e n tag r ff t
  let want ← PV_L2_F6NullWant.source isf ip ev
  PV_L2_F6NullFinish.source nm n f ok1 t want

def recorded (nm e : Slice U32) (n : Usize) (tag : Slice U32) (r f ff : Usize) (ok1 : Bool) (t : Usize) : Recorded (Bool × Usize) :=
  PV_L2_RecordCompact.bind (PV_L2_F6NullEntry.recorded e n tag r ff t) (fun entry =>
    PV_L2_RecordCompact.bind (PV_L2_F6NullWant.recorded entry.1 entry.2.1 entry.2.2)
      (fun want => PV_L2_F6NullFinish.recorded nm n f ok1 t want))

theorem recorded_erases (nm e : Slice U32) (n : Usize) (tag : Slice U32) (r f ff : Usize) (ok1 : Bool) (t : Usize) :
    (recorded nm e n tag r f ff ok1 t).value = step nm e n tag r f ff ok1 t := by
  unfold recorded step
  apply PV_L2_RecordRefinement.bind_erases
  · exact PV_L2_F6NullEntry.erases e n tag r ff t
  · intro entry
    rcases entry with ⟨isf,ip,ev⟩
    apply PV_L2_RecordRefinement.bind_erases
    · exact PV_L2_F6NullWant.erases isf ip ev
    · intro want
      exact PV_L2_F6NullFinish.erases nm n f ok1 t want

#print axioms recorded_erases

theorem unroll (nm e : Slice U32) (n : Usize) (tag : Slice U32) (r f ff : Usize) (ok1 : Bool) (t : Usize) :
    nvec_row_ok_loop nm e n tag r f ff ok1 t =
      if t<n then (do
        let (flag1,index1) ← step nm e n tag r f ff ok1 t
        nvec_row_ok_loop nm e n tag r f ff flag1 index1) else ok ok1 := by
  rw [nvec_row_ok_loop]
  split
  · simp only [step,PV_L2_F6NullEntry.source,PV_L2_F6NullWant.source,PV_L2_F6NullFinish.source,bind_assoc_eq,bind_tc_ok]
  · rfl

theorem increment (nm e : Slice U32) (n : Usize) (tag : Slice U32) (r f ff : Usize) (ok1 : Bool) (t : Usize) (after : Bool × Usize)
    (success : step nm e n tag r f ff ok1 t = ok after) : after.2.val=t.val+1 := by
  unfold step PV_L2_F6NullFinish.source at success
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
