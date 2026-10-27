import R1Z.PV_Src_PortEnumerateValues
set_option autoImplicit false
namespace R1Z.PV_Src_PortPairsMap
open Aeneas Aeneas.Std
variable {A B : Type}

theorem map (f : A → B) (xs : List A) (count : Usize) :
    (PV_Src_PortEnumerateTrace.pairs xs count).map (fun p => f p.2) = xs.map f := by
  induction xs generalizing count with
  | nil => rfl
  | cons x xs ih =>
    simp only [PV_Src_PortEnumerateTrace.pairs,List.map_cons,ih]

#print axioms map
end R1Z.PV_Src_PortPairsMap
