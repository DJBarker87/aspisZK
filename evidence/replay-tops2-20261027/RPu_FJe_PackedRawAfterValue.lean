import RPu_FJe_PackedRawAfter
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJe_PackedRawAfterValue
open Aeneas Aeneas.Std Result
open FJb_TailCell (cell)
open FJe_PackedRawAfter (Table words)
/-- All four source-order checked suffix values,composed without reducing a
concrete matrix or an unfolded recurrence. -/
theorem value (table : Table) (bound : U64) (out : Array U64 4#usize)
    (hb : ∀ r j,(words table r j).val<bound.val) (hw : 8*bound.val<2^64)
    (run : FJe_PackedRawAfter.source table bound=ok out) :
    ∀ j : Fin 4,(cell out j).val=PoseidonExternalPackedAlgebra.packedNat
      bound.val (fun r k=>(words table r k).val) j := by
  obtain ⟨x0,r0,v0⟩ := FJe_Component0.component0Ops_success bound (words table) hb hw
  obtain ⟨x1,r1,v1⟩ := FJe_Component1.component1Ops_success bound (words table) hb hw
  obtain ⟨x2,r2,v2⟩ := FJe_Component2.component2Ops_success bound (words table) hb hw
  obtain ⟨x3,r3,v3⟩ := FJe_Component3.component3Ops_success bound (words table) hb hw
  rw [FJe_PackedRawAfter.factor] at run
  simp only [FJe_PackedRawAfter.components,r0,r1,r2,r3,bind_tc_ok] at run
  have same : Array.make 4#usize [x0,x1,x2,x3]=out := Result.ok.inj run
  subst out
  intro j
  fin_cases j
  · simpa [cell,Array.make] using v0
  · simpa [cell,Array.make] using v1
  · simpa [cell,Array.make] using v2
  · simpa [cell,Array.make] using v3
#print axioms value
end AspisR1.FJe_PackedRawAfterValue
end
