import FJq_MainCells
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJq_ClaimRead
open Aeneas Aeneas.Std Result
open FIp_SemanticArithmetic (MQ)
/-- Every selected scalar is the SAME original source row and column. -/
theorem value (c : Array (Array MQ 29#usize) 3#usize) (j : Fin 3) (l : Fin 29)
    (row : Array MQ 29#usize) (x : MQ)
    (rr : Array.index_usize c (Usize.ofNatCore j.val (by have := j.isLt;scalar_tac))=ok row)
    (rx : Array.index_usize row (Usize.ofNatCore l.val (by have := l.isLt;scalar_tac))=ok x) :
    FIp_SemanticValues.decode x=FJn_MainClaims.claims c j l := by
  have rows:=FIr_ArrayRead.slot c _ row rr
  have cells:=FIr_ArrayRead.slot row _ x rx
  have rowEq : c.val[j.val]?=some row := by simpa using rows
  have cellEq : row.val[l.val]?=some x := by simpa using cells
  have er : c.val[j.val]'(by rw [c.property];exact j.isLt)=row := by
    exact Option.some.inj ((List.getElem?_eq_getElem (by rw [c.property];exact j.isLt)).symm.trans rowEq)
  unfold FJn_MainClaims.claims
  rw [er]
  have ex : row.val[l.val]'(by rw [row.property];exact l.isLt)=x := by
    exact Option.some.inj ((List.getElem?_eq_getElem (by rw [row.property];exact l.isLt)).symm.trans cellEq)
  rw [ex]
#print axioms value
end AspisR1.FJq_ClaimRead
end
