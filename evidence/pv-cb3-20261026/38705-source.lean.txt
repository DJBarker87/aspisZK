import R1Z.PV_CB3_StagedPacking
import R1Z.PV_CB3_StagedIndex
import R1Z.PV_CB3_ArrayEight
set_option autoImplicit false
namespace R1Z.PV_CB3_StagedHead
open Aeneas Aeneas.Std
open PV_CB3_StagedPacking PV_CB3_StagedIndex

theorem head_bits (rank : Array U32 8#usize) :
    (limb rank ⟨0,by decide⟩).bv = (bits rank).headD 0 := by
  obtain ⟨a,b,c,d,e,f,g,h,hview⟩ := PV_CB3_ArrayEight.view rank
  subst rank
  rfl
#print axioms head_bits
end R1Z.PV_CB3_StagedHead
