import R1Z.PV_L2_F6KDotStep

/-! Full extracted dot loop with arithmetic operands and indices retained.
Fuel is justified symbolically by n-p, never a changed source abort policy. -/
set_option autoImplicit false
namespace R1Z.PV_L2_F6KDot
open Aeneas Aeneas.Std Result R1CertCheck R1Z.CertCheck R1Z.PV_L2_Record
  R1Z.PV_L2_F6KDotStep

def loop (m : Slice U32) (st i : Usize) (idx : Slice U32) (io : Usize) (c : Slice U32) (co n : Usize) :
    Nat → U64 → Usize → Recorded U64
  | 0, acc, p => if p < n then ⟨.div,[.guard 0 p.val n.val true]⟩
    else ⟨ok acc,[.guard 0 p.val n.val false]⟩
  | fuel+1, acc, p => if p < n then do
      let _ ← operation (.guard 0 p.val n.val true) (ok ())
      let (acc1,p1) ← recorded m st i idx io c co acc p
      loop m st i idx io c co n fuel acc1 p1
    else ⟨ok acc,[.guard 0 p.val n.val false]⟩

theorem loop_erases (m : Slice U32) (st i : Usize) (idx : Slice U32) (io : Usize) (c : Slice U32) (co n : Usize)
    (fuel : Nat) (acc : U64) (p : Usize) (bound : n.val ≤ p.val+fuel) :
    (loop m st i idx io c co n fuel acc p).value = kdot_loop m st i idx io c co n acc p := by
  induction fuel generalizing acc p with
  | zero =>
    have hn : ¬p<n := by rw [UScalar.lt_equiv];omega
    rw [loop,if_neg hn,kdot_loop,if_neg hn]
  | succ fuel ih =>
    rw [loop,unroll]
    by_cases hn : p<n
    · rw [if_pos hn,if_pos hn]
      simp only [operation_bind_value,bind_tc_ok]
      change (PV_L2_Record.bind (recorded m st i idx io c co acc p)
        (fun pair => loop m st i idx io c co n fuel pair.1 pair.2)).value = _
      rw [bind_value,recorded_erases]
      cases hs : step m st i idx io c co acc p with
      | fail e => rfl
      | div => rfl
      | ok pair =>
        simp only [bind_tc_ok,Aeneas.Std.uncurry_apply_pair]
        exact ih pair.1 pair.2 (by have := increment m st i idx io c co acc p pair hs;omega)
    · rw [if_neg hn,if_neg hn]

def kdot (m : Slice U32) (st i : Usize) (idx : Slice U32) (io : Usize) (c : Slice U32) (co n : Usize) : Recorded U64 := do
  let acc ← loop m st i idx io c co n n.val 0#u64 0#usize
  operation (.rem acc.val P.val) (acc % P)

theorem kdot_erases (m : Slice U32) (st i : Usize) (idx : Slice U32) (io : Usize) (c : Slice U32) (co n : Usize) :
    (kdot m st i idx io c co n).value = R1CertCheck.kdot m st i idx io c co n := by
  change (PV_L2_Record.bind _ _).value = _
  rw [bind_value,loop_erases m st i idx io c co n n.val 0#u64 0#usize (by omega)]
  rfl

#print axioms loop_erases
#print axioms kdot_erases
end R1Z.PV_L2_F6KDot
