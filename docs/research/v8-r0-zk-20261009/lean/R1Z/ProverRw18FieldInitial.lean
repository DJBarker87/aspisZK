import R1Z.ProverRw18FieldMeaning
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw18FieldInitial
open Aeneas Aeneas.Std ProverRw18FieldMeaning

def base (tag : U32) : Raw := ⟨⟨tag,0#u32⟩,⟨0#u32,0#u32⟩⟩

theorem full_base (tag : U32) :
    full (base tag)=PV_RW_CompressLiftSelectors.initial tag := rfl

theorem canonical (tag : U32) (bound : tag.val<2147483647) : Canonical (base tag) :=
  ⟨⟨bound,by change (0 : Nat)<2147483647; decide⟩,⟨by change (0 : Nat)<2147483647; decide,by change (0 : Nat)<2147483647; decide⟩⟩

theorem decoded (tag : U32) : decode (base tag)=(tag.val : K) := by
  apply QuadraticAlgebra.ext
  · apply QuadraticAlgebra.ext <;> simp [base,decode,AspisR1.ExtractedCurrentQM31Exact.decode]
  · apply QuadraticAlgebra.ext <;> simp [base,decode,AspisR1.ExtractedCurrentQM31Exact.decode]

#print axioms full_base
#print axioms canonical
#print axioms decoded
end R1Z.ProverRw18FieldInitial
