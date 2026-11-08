import NNX_Gather
import LIB_VField
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNX_ClaimRead
open Aeneas Aeneas.Std Result AspisR1PublicPreparation LIB_VCarriers
/-- Bounded source indexing, normalized directly through Option reads. -/
theorem source (claims : Claims) (i : Usize) (bound : i.val < 29) :
 (do let row ← Array.index_usize (claimsRaw claims) 0#usize
     Array.index_usize row i) =
 .ok (LIB_VScalarCarriers.toRaw (LIB_VMask.cell claims ⟨i.val,bound⟩)) := by
 have rowBound : 0 < claims.val.length := by rw [claims.property];decide
 let row := claims.val[0]'rowBound
 have columnBound : i.val < row.val.length := by rw [row.property];exact bound
 simp only [Array.index_usize,Array.getElem?_Usize_eq,claimsRaw,k29Raw,
  LIB_VScalarCarriers.array,List.getElem?_map,
  show (0#usize).val=0 from rfl,List.getElem?_eq_getElem rowBound,
  Option.map_some,bind_tc_ok,LIB_VMask.cell]
 simp only [List.getElem?_eq_getElem columnBound,Option.map_some]
 rfl
#print axioms source
end AspisR1.NNX_ClaimRead
end
