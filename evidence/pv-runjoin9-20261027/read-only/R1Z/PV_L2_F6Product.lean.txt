import R1Z.PV_L2_F6ProductOuterStep
set_option autoImplicit false
namespace R1Z.PV_L2_F6Product
open Aeneas Aeneas.Std Result R1CertCheck R1Z.CertCheck R1Z.PV_L2_Record
  R1Z.PV_L2_F6ProductOuterStep
def loop (a : Slice U32) (ao : Usize) (b : Slice U32) (bo : Usize)
    (c : Slice U32) (co ni nj len : Usize) :
    Nat → Bool → Usize → Recorded Bool
  | 0, flag, p => if p<ni then ⟨.div,[.guard 3 p.val ni.val true]⟩
      else ⟨ok flag,[.guard 3 p.val ni.val false]⟩
  | fuel+1, flag, p => if p<ni then do
      let _ ← operation (.guard 3 p.val ni.val true) (ok ())
      let (flag1,p1) ← recorded a ao b bo c co nj len flag p
      loop a ao b bo c co ni nj len fuel flag1 p1
    else ⟨ok flag,[.guard 3 p.val ni.val false]⟩

theorem loop_erases (a : Slice U32) (ao : Usize) (b : Slice U32) (bo : Usize)
    (c : Slice U32) (co ni nj len : Usize)
    (fuel : Nat) (flag : Bool) (p : Usize) (bound : ni.val≤p.val+fuel) :
    (loop a ao b bo c co ni nj len fuel flag p).value = prod_ok_loop a ao b bo c co ni nj len flag p := by
  induction fuel generalizing flag p with
  | zero =>
    have hn : ¬p<ni := by rw [UScalar.lt_equiv];omega
    rw [loop,if_neg hn,prod_ok_loop,if_neg hn]
  | succ fuel ih =>
    rw [loop,unroll]
    by_cases hn : p<ni
    · rw [if_pos hn,if_pos hn]
      simp only [operation_bind_value,bind_tc_ok]
      change (PV_L2_Record.bind (recorded a ao b bo c co nj len flag p)
        (fun pair => loop a ao b bo c co ni nj len fuel pair.1 pair.2)).value = _
      rw [bind_value,recorded_erases]
      cases hs : step a ao b bo c co nj len flag p with
      | fail e => rfl
      | div => rfl
      | ok pair =>
        simp only [bind_tc_ok]
        exact ih pair.1 pair.2 (by have := increment a ao b bo c co nj len flag p pair hs;omega)
    · rw [if_neg hn,if_neg hn]

theorem product_erases (a : Slice U32) (ao : Usize) (b : Slice U32) (bo : Usize)
    (c : Slice U32) (co ni nj len : Usize) :
    (loop a ao b bo c co ni nj len ni.val true 0#usize).value = prod_ok a ao b bo c co ni nj len := by
  exact loop_erases a ao b bo c co ni nj len ni.val true 0#usize (by omega)

#print axioms loop_erases
#print axioms product_erases
end R1Z.PV_L2_F6Product
