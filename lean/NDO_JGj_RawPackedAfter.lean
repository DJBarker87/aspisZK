import RPv_FJe_PackedRawAfter
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGj_RawPackedAfter
open Aeneas Aeneas.Std Result
/-- Construct the exact raw suffix forward, using the existing component safety proofs. -/
theorem source (table : FJe_PackedRawAfter.Table) (bound : U64)
    (hb : ∀ r j,(FJe_PackedRawAfter.words table r j).val<bound.val)
    (hw : 8*bound.val<2^64) :
    ∃ out,FJe_PackedRawAfter.source table bound=ok out := by
  obtain ⟨x0,h0,_⟩ := FJe_Component0.component0Ops_success bound (FJe_PackedRawAfter.words table) hb hw
  obtain ⟨x1,h1,_⟩ := FJe_Component1.component1Ops_success bound (FJe_PackedRawAfter.words table) hb hw
  obtain ⟨x2,h2,_⟩ := FJe_Component2.component2Ops_success bound (FJe_PackedRawAfter.words table) hb hw
  obtain ⟨x3,h3,_⟩ := FJe_Component3.component3Ops_success bound (FJe_PackedRawAfter.words table) hb hw
  refine ⟨Array.make 4#usize [x0,x1,x2,x3],?_⟩
  rw [FJe_PackedRawAfter.factor]
  simp only [FJe_PackedRawAfter.components,h0,h1,h2,h3,bind_tc_ok]
#print axioms source
end AspisR1.JGj_RawPackedAfter
end
