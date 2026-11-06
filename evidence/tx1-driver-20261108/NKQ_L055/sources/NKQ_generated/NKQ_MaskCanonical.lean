import NKQ_MaskArrays
import NKQ_MaskCuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKQ_MaskCanonical
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NKQ_ArrayWindows NKQ_MaskCuts

theorem claim_cell (c : Claims) (canonical : CanonClaims c)
 (row col : Nat) (hr : row<3) (hc : col<29) :
 Canon (cell (cell c row hr) col hc) := by
 apply canonical (cell c row hr) (List.getElem_mem _)
 exact List.getElem_mem _

theorem low (c : Claims) (canonical : CanonClaims c) :
 ∀ q∈(NKQ_MaskArrays.lowArray c).val,Canon q := by
 intro value member
 obtain ⟨index,member,rfl⟩:=List.mem_map.mp member
 have bound:=NKQ_FromFnIndices.bound 16#usize index member
 have small : index.val<16 := by simpa using bound
 simp only [NKQ_MaskArrays.lowValue,dif_pos small,NKQ_MaskLowStep.lowAt]
 exact claim_cell c canonical 0 index.val (by decide) (by omega)

theorem high (c : Claims) (canonical : CanonClaims c) :
 ∀ q∈(NKQ_MaskArrays.highArray c).val,Canon q := by
 intro value member
 obtain ⟨index,member,rfl⟩:=List.mem_map.mp member
 have bound:=NKQ_FromFnIndices.bound 10#usize index member
 have small : index.val<10 := by simpa using bound
 simp only [NKQ_MaskArrays.highValue,dif_pos small,NKQ_MaskHighStep.highAt]
 exact claim_cell c canonical 0 (16+index.val) (by decide) (by omega)

/-- Complete canonical domains of the two concrete SAME-claims mask arrays;
blind and alpha remain the caller's SAME values, never a new payload seed. -/
theorem domain (c : Claims) (a : Alpha) (cc : CanonClaims c) (ca : CanonAlpha a) :
 (∀ q∈(NKQ_MaskArrays.lowArray c).val,Canon q) ∧
 (∀ q∈(NKQ_MaskArrays.highArray c).val,Canon q) ∧ Canon (blind c) ∧ CanonAlpha a :=
 ⟨low c cc,high c cc,claim_cell c cc 0 27 (by decide) (by decide),ca⟩
#print axioms claim_cell
#print axioms low
#print axioms high
#print axioms domain
end AspisR1.NKQ_MaskCanonical
end
