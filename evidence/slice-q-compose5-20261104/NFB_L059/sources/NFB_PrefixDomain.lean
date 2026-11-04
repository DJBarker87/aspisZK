import NFB_TerminalCuts
set_option autoImplicit false
noncomputable section
namespace NFB_PrefixDomain
open Aeneas Aeneas.Std Result AspisR1
open NEW_GeometryDictionary

theorem model_length (flat prefixes : List U32) (product : U32) :
 (S7Kani2PrefixLoop.model flat prefixes product).1.length=prefixes.length+flat.length := by
 induction flat generalizing prefixes product with
 | nil => simp [S7Kani2PrefixLoop.model]
 | cons x xs ih =>
  rw [S7Kani2PrefixLoop.model,ih]
  simp only [List.length_append,List.length_singleton,List.length_cons]
  omega

theorem complete (flat : alloc.vec.Vec U32) (bound : flat.val.length≤110) :
 ∃ (prefixes : alloc.vec.Vec U32) (product : U32),
 adopted.op13 flat.deref=ok (prefixes,product) ∧ prefixes.val.length=flat.val.length := by
 obtain ⟨prefixes,product,run,meaning⟩ := Port4C_PrefixMeaning.total
  NEW_GeometryPrefix.leaves rfl rfl flat.deref bound
 refine ⟨prefixes,product,?_,?_⟩
 · exact run
 · have values:=congrArg (fun p : List U32 × U32=>p.1.length) meaning
   rw [model_length] at values
   simpa only [List.length_nil,Nat.zero_add] using values
#print axioms model_length
#print axioms complete
end NFB_PrefixDomain
end
