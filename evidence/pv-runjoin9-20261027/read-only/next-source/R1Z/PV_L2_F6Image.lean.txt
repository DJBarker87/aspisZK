import R1Z.PV_L2_F6ImageStep
set_option autoImplicit false
namespace R1Z.PV_L2_F6Image
open Aeneas Aeneas.Std Result R1CertCheck R1Z.CertCheck R1Z.PV_L2_Record
  R1Z.PV_L2_F6ImageStep
def loop (m : Slice U32) (st nrows j : Usize) (idx : Slice U32) (io : Usize)
    (c : Slice U32) (co s : Usize) (tgt : Slice U32) (to1 ts : Usize) :
    Nat → Bool → Usize → Recorded Bool
  | 0, flag, p => if p<nrows then ⟨.div,[.guard 3 p.val nrows.val true]⟩
      else ⟨ok flag,[.guard 3 p.val nrows.val false]⟩
  | fuel+1, flag, p => if p<nrows then do
      let _ ← operation (.guard 3 p.val nrows.val true) (ok ())
      let (flag1,p1) ← recorded m st j idx io c co s tgt to1 ts flag p
      loop m st nrows j idx io c co s tgt to1 ts fuel flag1 p1
    else ⟨ok flag,[.guard 3 p.val nrows.val false]⟩

theorem loop_erases (m : Slice U32) (st nrows j : Usize) (idx : Slice U32) (io : Usize)
    (c : Slice U32) (co s : Usize) (tgt : Slice U32) (to1 ts : Usize)
    (fuel : Nat) (flag : Bool) (p : Usize) (bound : nrows.val≤p.val+fuel) :
    (loop m st nrows j idx io c co s tgt to1 ts fuel flag p).value = kimg_ok_loop m st nrows j idx io c co s tgt to1 ts flag p := by
  induction fuel generalizing flag p with
  | zero =>
    have hn : ¬p<nrows := by rw [UScalar.lt_equiv];omega
    rw [loop,if_neg hn,kimg_ok_loop,if_neg hn]
  | succ fuel ih =>
    rw [loop,unroll]
    by_cases hn : p<nrows
    · rw [if_pos hn,if_pos hn]
      simp only [operation_bind_value,bind_tc_ok]
      change (PV_L2_Record.bind (recorded m st j idx io c co s tgt to1 ts flag p)
        (fun pair => loop m st nrows j idx io c co s tgt to1 ts fuel pair.1 pair.2)).value = _
      rw [bind_value,recorded_erases]
      cases hs : step m st j idx io c co s tgt to1 ts flag p with
      | fail e => rfl
      | div => rfl
      | ok pair =>
        simp only [bind_tc_ok]
        exact ih pair.1 pair.2 (by have := increment m st j idx io c co s tgt to1 ts flag p pair hs;omega)
    · rw [if_neg hn,if_neg hn]

theorem image_erases (m : Slice U32) (st nrows j : Usize) (idx : Slice U32) (io : Usize)
    (c : Slice U32) (co s : Usize) (tgt : Slice U32) (to1 ts : Usize) :
    (loop m st nrows j idx io c co s tgt to1 ts nrows.val true 0#usize).value = kimg_ok m st nrows j idx io c co s tgt to1 ts := by
  exact loop_erases m st nrows j idx io c co s tgt to1 ts nrows.val true 0#usize (by omega)

#print axioms loop_erases
#print axioms image_erases
end R1Z.PV_L2_F6Image
