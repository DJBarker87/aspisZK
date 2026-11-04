import NEV_BorrowMaps
import NEV_CtorNormalization
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace NEV_WeightDomains
open Aeneas Aeneas.Std Result NEV_AccumulateCarriers

def Canonical (v : alloc.vec.Vec RawQ) : Prop := ∀ q∈v.val,NBF_PowerStep.Canonical (toQ q)
/-- SAME actual read establishes the canonical embedding callback domain. -/
theorem read (v : alloc.vec.Vec RawQ) (index : Usize) (inside : index.val<v.val.length)
    (q : RawQ) (run : NEV_AccumulateRaw.accumulated_weight_at v.deref index=ok q)
    (canonical : Canonical v) :
    NEV_CtorNormalization.Canonical (NEV_AccumulateRaw.NEV_Bindings.toCtorQ q) := by
  obtain ⟨actual,actualRun,point⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.index_usize_spec v index inside)
  have sourceRun : NEV_AccumulateRaw.accumulated_weight_at v.deref index=ok actual := actualRun
  have same : actual=q := Result.ok.inj (sourceRun.symm.trans run)
  have member : q∈v.val := by
    have equality : q=v.val[index.val]'inside := same.symm.trans point
    rw [equality]
    exact List.getElem_mem _
  have values := canonical q member
  exact ⟨⟨values 0,values 1⟩,⟨values 2,values 3⟩⟩
#print axioms read
end NEV_WeightDomains
end
