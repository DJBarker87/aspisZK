import R1Z.PV_L2_F6ProductStep
set_option autoImplicit false
namespace R1Z.PV_L2_F6ProductRow
open Aeneas Aeneas.Std Result R1CertCheck R1Z.CertCheck R1Z.PV_L2_Record
  R1Z.PV_L2_F6ProductStep
def loop (a : Slice U32) (ao : Usize) (b : Slice U32) (bo : Usize)
    (c : Slice U32) (co i nj len : Usize) :
    Nat → Bool → Usize → Recorded Bool
  | 0, flag, p => if p<nj then ⟨.div,[.guard 3 p.val nj.val true]⟩
      else ⟨ok flag,[.guard 3 p.val nj.val false]⟩
  | fuel+1, flag, p => if p<nj then do
      let _ ← operation (.guard 3 p.val nj.val true) (ok ())
      let (flag1,p1) ← recorded a ao b bo c co i nj len flag p
      loop a ao b bo c co i nj len fuel flag1 p1
    else ⟨ok flag,[.guard 3 p.val nj.val false]⟩

theorem loop_erases (a : Slice U32) (ao : Usize) (b : Slice U32) (bo : Usize)
    (c : Slice U32) (co i nj len : Usize)
    (fuel : Nat) (flag : Bool) (p : Usize) (bound : nj.val≤p.val+fuel) :
    (loop a ao b bo c co i nj len fuel flag p).value = prod_row_ok_loop a ao b bo c co i nj len flag p := by
  induction fuel generalizing flag p with
  | zero =>
    have hn : ¬p<nj := by rw [UScalar.lt_equiv];omega
    rw [loop,if_neg hn,prod_row_ok_loop,if_neg hn]
  | succ fuel ih =>
    rw [loop,unroll]
    by_cases hn : p<nj
    · rw [if_pos hn,if_pos hn]
      simp only [operation_bind_value,bind_tc_ok]
      change (PV_L2_Record.bind (recorded a ao b bo c co i nj len flag p)
        (fun pair => loop a ao b bo c co i nj len fuel pair.1 pair.2)).value = _
      rw [bind_value,recorded_erases]
      cases hs : step a ao b bo c co i nj len flag p with
      | fail e => rfl
      | div => rfl
      | ok pair =>
        simp only [bind_tc_ok]
        exact ih pair.1 pair.2 (by have := increment a ao b bo c co i nj len flag p pair hs;omega)
    · rw [if_neg hn,if_neg hn]

theorem row_erases (a : Slice U32) (ao : Usize) (b : Slice U32) (bo : Usize)
    (c : Slice U32) (co i nj len : Usize) :
    (loop a ao b bo c co i nj len nj.val true 0#usize).value = prod_row_ok a ao b bo c co i nj len := by
  exact loop_erases a ao b bo c co i nj len nj.val true 0#usize (by omega)

#print axioms loop_erases
#print axioms row_erases
end R1Z.PV_L2_F6ProductRow
