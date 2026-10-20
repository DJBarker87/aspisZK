import GeometryInputsEntry
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1GeometryInputs.Proof

theorem flat_slot (records : List InputRecord) (i j : Nat)
    (hi : i<records.length) (hj : j<5) :
    (records.flatMap (fun e => e.1.val)).getD (5*i+j) 0#u32 =
      (records[i]).1.val.getD j 0#u32 := by
  induction records generalizing i with
  | nil => simp at hi
  | cons r rs ih =>
    have h5 : r.1.val.length=5 := r.1.property
    cases i with
    | zero =>
      simp only [List.flatMap_cons,Nat.mul_zero,Nat.zero_add,List.getElem_cons_zero]
      change (r.1.val ++ rs.flatMap (fun e => e.1.val)).getD j 0#u32 = r.1.val.getD j 0#u32
      have hb : j<r.1.val.length := by rw [h5]; exact hj
      simp only [List.getD_eq_getElem?_getD,List.getElem?_append_left hb]
    | succ i =>
      have hi' : i<rs.length := by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using hi
      simp only [List.flatMap_cons,List.getElem_cons_succ]
      change (r.1.val ++ rs.flatMap (fun e => e.1.val)).getD (5*(i+1)+j) 0#u32 =
        (rs[i]'hi').1.val.getD j 0#u32
      have hg : r.1.val.length ≤ 5*(i+1)+j := by rw [h5]; omega
      have hs : 5*(i+1)+j-r.1.val.length = 5*i+j := by rw [h5]; omega
      simp only [List.getD_eq_getElem?_getD,List.getElem?_append_right hg,hs]
      exact ih i hi'

#print axioms flat_slot
end AspisR1GeometryInputs.Proof
