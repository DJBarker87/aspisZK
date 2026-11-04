import NFQ_StatementLaws
set_option autoImplicit false
namespace NFQ_StatementDomains
open Aeneas Aeneas.Std Result
open FIq_Native.pool_v1

theorem output_range (v : pair_forest_semantic_terminal.CompiledVariant) :
 ∃ out, pair_forest_semantic_terminal.variant_expected_output v=ok out ∧ out.val≤1 := by
 cases v <;> (refine ⟨_,rfl,?_⟩; scalar_tac)

theorem limb_domains (v : FIq_Native.field.QM31)
 (h : v.c0.a.val<2147483647 ∧ v.c0.b.val<2147483647 ∧
      v.c1.a.val<2147483647 ∧ v.c1.b.val<2147483647) :
 ∃ out, FIq_Native.state_only_poseidon.extension_limbs v=ok out ∧
   ∀ x ∈ out.val,x.val<2147483647 := by
 refine ⟨Array.make 4#usize [v.c0.a,v.c0.b,v.c1.a,v.c1.b],rfl,?_⟩
 intro x hx
 change x ∈ [v.c0.a,v.c0.b,v.c1.a,v.c1.b] at hx
 simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
 rcases hx with rfl | rfl | rfl | rfl
 · exact h.1
 · exact h.2.1
 · exact h.2.2.1
 · exact h.2.2.2
#print axioms output_range
#print axioms limb_domains
end NFQ_StatementDomains
