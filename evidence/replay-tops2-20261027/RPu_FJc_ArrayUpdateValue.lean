import RPu_FIp_ArrayValue
import RPt_FJc_ReadSlot
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJc_ArrayUpdateValue
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open FIo_FieldBridge (NE wide)

theorem value {N : Usize} (a b : Array NE N) (i : Usize) (z : NE) (j : Nat)
    (run : Array.update a i z=ok b) :
    FIp_ArrayValue.value b j=if i.val=j then decodeWide (wide z) else FIp_ArrayValue.value a j := by
  unfold Array.update at run
  split at run
  · cases run
  · rename_i h
    cases Result.ok.inj run
    have hi : i.val<a.val.length := by
      change a.val[i.val]?=some _ at h
      exact (List.getElem_of_getElem? h).choose
    simp only [FIp_ArrayValue.value,List.getElem?_set]
    by_cases eq : i.val=j
    · have hj : j<a.val.length := eq ▸ hi
      simp only [eq,if_pos hj,if_true]
    · simp only [eq,if_false]
#print axioms value
end AspisR1.FJc_ArrayUpdateValue
end
