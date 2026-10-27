import R1Z.PV_L2_F6DotStep

/-! Full extracted dot loop with arithmetic operands and indices retained.
Fuel is justified symbolically by n-p, never a changed source abort policy. -/
set_option autoImplicit false
namespace R1Z.PV_L2_F6Dot
open Aeneas Aeneas.Std Result R1CertCheck R1Z.CertCheck R1Z.PV_L2_Record
  R1Z.PV_L2_F6DotStep

def loop (a : Slice U32) (ao ast : Usize) (b : Slice U32) (bo bst n : Usize) :
    Nat → U64 → Usize → Recorded U64
  | 0, acc, p => if p < n then ⟨.div,[.guard 0 p.val n.val true]⟩
    else ⟨ok acc,[.guard 0 p.val n.val false]⟩
  | fuel+1, acc, p => if p < n then do
      let _ ← operation (.guard 0 p.val n.val true) (ok ())
      let (acc1,p1) ← recorded a ao ast b bo bst acc p
      loop a ao ast b bo bst n fuel acc1 p1
    else ⟨ok acc,[.guard 0 p.val n.val false]⟩

theorem loop_erases (a : Slice U32) (ao ast : Usize) (b : Slice U32) (bo bst n : Usize)
    (fuel : Nat) (acc : U64) (p : Usize) (bound : n.val ≤ p.val+fuel) :
    (loop a ao ast b bo bst n fuel acc p).value = dot_loop a ao ast b bo bst n acc p := by
  induction fuel generalizing acc p with
  | zero =>
    have hn : ¬p<n := by rw [UScalar.lt_equiv];omega
    rw [loop,if_neg hn,dot_loop,if_neg hn]
  | succ fuel ih =>
    rw [loop,unroll]
    by_cases hn : p<n
    · rw [if_pos hn,if_pos hn]
      simp only [operation_bind_value,bind_tc_ok]
      change (PV_L2_Record.bind (recorded a ao ast b bo bst acc p)
        (fun pair => loop a ao ast b bo bst n fuel pair.1 pair.2)).value = _
      rw [bind_value,recorded_erases]
      cases hs : step a ao ast b bo bst acc p with
      | fail e => rfl
      | div => rfl
      | ok pair =>
        simp only [bind_tc_ok,Aeneas.Std.uncurry_apply_pair]
        exact ih pair.1 pair.2 (by have := increment a ao ast b bo bst acc p pair hs;omega)
    · rw [if_neg hn,if_neg hn]

def dot (a : Slice U32) (ao ast : Usize) (b : Slice U32) (bo bst n : Usize) : Recorded U64 := do
  let acc ← loop a ao ast b bo bst n n.val 0#u64 0#usize
  operation (.rem acc.val P.val) (acc % P)

theorem dot_erases (a : Slice U32) (ao ast : Usize) (b : Slice U32) (bo bst n : Usize) :
    (dot a ao ast b bo bst n).value = R1CertCheck.dot a ao ast b bo bst n := by
  change (PV_L2_Record.bind _ _).value = _
  rw [bind_value,loop_erases a ao ast b bo bst n n.val 0#u64 0#usize (by omega)]
  rfl

#print axioms loop_erases
#print axioms dot_erases
end R1Z.PV_L2_F6Dot
