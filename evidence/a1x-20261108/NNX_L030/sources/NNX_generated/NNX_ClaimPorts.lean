import NNX_ClaimIndex
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNX_ClaimPorts
open Aeneas Aeneas.Std Result AspisR1PublicPreparation LIB_VCarriers
abbrev first (c : Claims) : K29 := c.val[0]'(by rw [c.property];decide)

theorem row (c : Claims) :
 Array.index_usize (claimsRaw c) 0#usize = .ok (k29Raw (first c)) := by
 rw [NNX_ArrayRead.source _ _ (by rw [(claimsRaw c).property];decide)]
 rfl

theorem at27 (c : Claims) :
 Array.index_usize (k29Raw (first c)) 27#usize = .ok (LIB_VField.g c) := by
 rw [NNX_ArrayRead.source _ _ (by rw [(k29Raw (first c)).property];decide)]
 simp only [k29Raw,LIB_VScalarCarriers.array,List.getElem_map,LIB_VField.g,LIB_VMask.cell,first]
 rfl
#print axioms row
#print axioms at27
end AspisR1.NNX_ClaimPorts
end
