import R1Z.PV_L2_Record

/-! The exact extracted pivot-lane check, with retained index/error prefixes.
This is one native-source checker component, not the full P_R1 certificate. -/
set_option autoImplicit false
namespace R1Z.PV_L2_F6Pivot
open Aeneas Aeneas.Std Result R1CertCheck R1Z.CertCheck R1Z.PV_L2_Record

def step (idx : Slice U32) (io : Usize) (lane : Slice U32) (lj : U32)
    (flag : Bool) (p : Usize) : Result (Bool × Usize) := do
  let i ← io + p
  let i1 ← Slice.index_usize idx i
  let t ← lift (UScalar.cast .Usize i1)
  let i2 ← Slice.index_usize lane t
  let p1 ← p + 1#usize
  ok (flag && (i2=lj),p1)

def recorded (idx : Slice U32) (io : Usize) (lane : Slice U32) (lj : U32)
    (flag : Bool) (p : Usize) : Recorded (Bool × Usize) := do
  let i ← operation (.add io.val p.val) (io+p)
  let i1 ← operation (.index 0 i.val) (Slice.index_usize idx i)
  let t := UScalar.cast .Usize i1
  let i2 ← operation (.index 1 t.val) (Slice.index_usize lane t)
  let p1 ← operation (.add p.val 1) (p+1#usize)
  operation (.guard 2 i2.val lj.val (i2=lj)) (ok (flag && (i2=lj),p1))

theorem recorded_erases (idx : Slice U32) (io : Usize) (lane : Slice U32) (lj : U32)
    (flag : Bool) (p : Usize) :
    (recorded idx io lane lj flag p).value = step idx io lane lj flag p := by
  simp only [recorded,step,operation_bind_value,operation_value,lift,bind_tc_ok]

theorem unroll (idx : Slice U32) (io s : Usize) (lane : Slice U32) (lj : U32)
    (flag : Bool) (p : Usize) : piv_ok_loop idx io s lane lj flag p =
      if p<s then (do
        let (flag1,p1) ← step idx io lane lj flag p
        piv_ok_loop idx io s lane lj flag1 p1) else ok flag := by
  rw [piv_ok_loop]
  split
  · simp only [step,bind_assoc_eq,bind_tc_ok]
  · rfl

theorem increment (idx : Slice U32) (io : Usize) (lane : Slice U32) (lj : U32)
    (flag : Bool) (p : Usize) (after : Bool × Usize)
    (success : step idx io lane lj flag p = ok after) : after.2.val=p.val+1 := by
  unfold step at success
  obtain ⟨i,hi,success⟩ := bind_eq_ok success
  obtain ⟨i1,hi1,success⟩ := bind_eq_ok success
  obtain ⟨t,ht,success⟩ := bind_eq_ok success
  obtain ⟨i2,hi2,success⟩ := bind_eq_ok success
  obtain ⟨p1,hp1,success⟩ := bind_eq_ok success
  have he := ok_inj success
  rw [← he]
  simpa only [show (1#usize).val=1 from rfl] using add_ok hp1

def loop (idx : Slice U32) (io s : Usize) (lane : Slice U32) (lj : U32) :
    Nat → Bool → Usize → Recorded Bool
  | 0, flag, p => if p<s then ⟨.div,[.guard 3 p.val s.val true]⟩
      else ⟨ok flag,[.guard 3 p.val s.val false]⟩
  | fuel+1, flag, p => if p<s then do
      let _ ← operation (.guard 3 p.val s.val true) (ok ())
      let (flag1,p1) ← recorded idx io lane lj flag p
      loop idx io s lane lj fuel flag1 p1
    else ⟨ok flag,[.guard 3 p.val s.val false]⟩

theorem loop_erases (idx : Slice U32) (io s : Usize) (lane : Slice U32) (lj : U32)
    (fuel : Nat) (flag : Bool) (p : Usize) (bound : s.val≤p.val+fuel) :
    (loop idx io s lane lj fuel flag p).value = piv_ok_loop idx io s lane lj flag p := by
  induction fuel generalizing flag p with
  | zero =>
    have hn : ¬p<s := by rw [UScalar.lt_equiv];omega
    rw [loop,if_neg hn,piv_ok_loop,if_neg hn]
  | succ fuel ih =>
    rw [loop,unroll]
    by_cases hn : p<s
    · rw [if_pos hn,if_pos hn]
      simp only [operation_bind_value,bind_tc_ok]
      change (PV_L2_Record.bind (recorded idx io lane lj flag p)
        (fun pair => loop idx io s lane lj fuel pair.1 pair.2)).value = _
      rw [bind_value,recorded_erases]
      cases hs : step idx io lane lj flag p with
      | fail e => rfl
      | div => rfl
      | ok pair =>
        simp only [bind_tc_ok]
        exact ih pair.1 pair.2 (by have := increment idx io lane lj flag p pair hs;omega)
    · rw [if_neg hn,if_neg hn]

theorem piv_erases (idx : Slice U32) (io s : Usize) (lane : Slice U32) (lj : U32) :
    (loop idx io s lane lj s.val true 0#usize).value = piv_ok idx io s lane lj := by
  exact loop_erases idx io s lane lj s.val true 0#usize (by omega)

#print axioms recorded_erases
#print axioms unroll
#print axioms increment
#print axioms loop_erases
#print axioms piv_erases
end R1Z.PV_L2_F6Pivot
