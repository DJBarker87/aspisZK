import NNX_Gather
import LIB_VField
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNX_ClaimCell
open Aeneas Aeneas.Std Result AspisR1PublicPreparation LIB_VCarriers
/-- Symbolic row-zero access at an arbitrary bounded column. -/
theorem source (claims : Claims) (i : Usize) (bound : i.val < 29) :
 (do let row ← Array.index_usize (claimsRaw claims) 0#usize
     Array.index_usize row i) =
 .ok (LIB_VScalarCarriers.toRaw (LIB_VMask.cell claims ⟨i.val,bound⟩)) := by
 have row := WP.spec_imp_exists (Array.index_usize_spec (claimsRaw claims) 0#usize (by
  rw [(claimsRaw claims).property]; decide))
 obtain ⟨r,hr,er⟩ := row
 rw [hr,bind_tc_ok]
 have item := WP.spec_imp_exists (Array.index_usize_spec r i (by
  rw [r.property]; exact bound))
 obtain ⟨v,hv,ev⟩ := item
 rw [hv]
 congr 1
 rw [ev,er]
 simp only [claimsRaw,k29Raw,LIB_VScalarCarriers.array,List.getElem_map,LIB_VMask.cell]
 rfl
#print axioms source
end AspisR1.NNX_ClaimCell
end
