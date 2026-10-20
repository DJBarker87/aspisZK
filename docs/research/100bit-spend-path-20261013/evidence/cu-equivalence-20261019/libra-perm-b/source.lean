import CuSavingsLibraSourceControl
set_option autoImplicit false
namespace AspisR1.CuSavingsLibraSourcePerm
open Aeneas Aeneas.Std Result AspisR1Libra
open CuSavingsLibraSourceControl

def perm (i : Nat) : Nat := [0,3,2,1].getD i 0

theorem source (i : Usize) (hi : i.val<4) :
    ∃ out, Array.index_usize PERM i=.ok out ∧ out.val<4 ∧ out.val=perm i.val := by
  let out := lookup PERM 0#usize i.val
  have hr := read PERM 0#usize i (by scalar_tac)
  refine ⟨out,hr,?_,?_⟩
  all_goals
    have hc : i.val=0 ∨ i.val=1 ∨ i.val=2 ∨ i.val=3 := by omega
    rcases hc with h | h | h | h <;>
      simp only [out,lookup,PERM,Array.make,perm,h,List.getD,
        UScalar.ofNatCore_val_eq] <;> decide

#print axioms source
end AspisR1.CuSavingsLibraSourcePerm
