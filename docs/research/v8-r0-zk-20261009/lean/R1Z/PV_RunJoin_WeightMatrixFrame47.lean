import R1Z.PV_RunJoin_WeightArrayUpdate47
import R1Z.PV_RunJoin_WeightMutation47
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightMatrixFrame47
open Aeneas Aeneas.Std Result
open PV_RunJoin_WeightFactorWrite47 (Matrix)
open PV_B2_F_ConstructorCarrier (K)

def Frame (m m1 : Matrix) (start n : Nat) : Prop :=
  ∀ i, i < 5 → (i < start ∨ start + n ≤ i) → m.val[i]? = m1.val[i]?

theorem done (m m1 : Matrix) (start : Nat) (h : Frame m m1 start 0) : m=m1 := by
  apply Subtype.ext
  apply List.ext_getElem?
  intro i
  by_cases hi : i<5
  · exact h i hi (by omega)
  · rw [List.getElem?_eq_none (by rw [m.property];scalar_tac),
      List.getElem?_eq_none (by rw [m1.property];scalar_tac)]
#print axioms done

theorem step (m m1 : Matrix) (d : Usize) (n : Nat) (row : Array K 4#usize)
    (hd : d.val<5) (h : Frame m m1 d.val (n+1)) :
    Frame (Aeneas.Std.Array.set m d row) (Aeneas.Std.Array.set m1 d row) (d.val+1) n := by
  intro i hi hf
  change (m.val.set d.val row)[i]?=(m1.val.set d.val row)[i]?
  by_cases he : i=d.val
  · subst i
    rw [List.getElem?_set_self (by rw [m.property];exact hd),
      List.getElem?_set_self (by rw [m1.property];exact hd)]
  · rw [PV_B2_F_ArrayMutation.untouched _ _ _ _ (by omega),
      PV_B2_F_ArrayMutation.untouched _ _ _ _ (by omega)]
    exact h i hi (by omega)
#print axioms step
end R1Z.PV_RunJoin_WeightMatrixFrame47
