import NNX_ArrayRead
import LIB_VField
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNX_ClaimIndex
open Aeneas Aeneas.Std Result AspisR1PublicPreparation LIB_VCarriers

theorem source (claims : Claims) (i : Usize) (bound : i.val < 29) :
 (do let row ← Array.index_usize (claimsRaw claims) 0#usize
     Array.index_usize row i) =
 .ok (LIB_VScalarCarriers.toRaw (LIB_VMask.cell claims ⟨i.val,bound⟩)) := by
 have rb : (0#usize).val < (claimsRaw claims).val.length := by
  rw [(claimsRaw claims).property];decide
 rw [NNX_ArrayRead.source (claimsRaw claims) 0#usize rb,bind_tc_ok]
 have cb : i.val < ((claimsRaw claims).val[(0#usize).val]'rb).val.length := by
  rw [((claimsRaw claims).val[(0#usize).val]'rb).property];exact bound
 rw [NNX_ArrayRead.source _ i cb]
 congr 1
 simp only [claimsRaw,k29Raw,LIB_VScalarCarriers.array,List.getElem_map,LIB_VMask.cell]
 rfl
#print axioms source
end AspisR1.NNX_ClaimIndex
end
