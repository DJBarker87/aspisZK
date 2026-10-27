import R1Z.PV_Src_PortNodeCopy
set_option autoImplicit false
namespace R1Z.PV_Src_PortJoinedWords
open Aeneas Aeneas.Std

theorem source (left right : Array U32 8#usize) (j : Fin 16) :
    (PV_Src_PortNodeCopy.joined left right).val[j.val]! =
      if j.val<8 then left.val[j.val]! else right.val[j.val-8]! := by
  rw [PV_Src_PortDigestEta.source left,PV_Src_PortDigestEta.source right]
  fin_cases j <;> rfl

#print axioms source
end R1Z.PV_Src_PortJoinedWords
