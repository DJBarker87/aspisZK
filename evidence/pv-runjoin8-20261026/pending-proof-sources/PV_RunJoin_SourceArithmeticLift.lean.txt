import R1Z.PV_Src_ExternalMat4Copy
set_option autoImplicit false
namespace R1Z.PV_RunJoin_SourceArithmeticLift
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
variable {K : Type} [Field K] [CharP K 2147483647]

/-- Full wrapping-source scalar reduction, with totality, canonical words and
field meaning together. There is no input-range or source-success premise. -/
theorem reduce (x : U64) :
    ∃ out, AspisBuilderPoseidonReference.aspis_core.field.M31.reduce_u62 x = ok out ∧
      out.val < 2147483647 ∧ liftU (K := K) out = (x.val : K) := by
  refine ⟨PV_Src_ScalarReduce.value x,PV_Src_ScalarReduce.reference_eq x,
    PV_Src_ScalarReduce.canonical x,?_⟩
  change ((PV_Src_ScalarReduce.value x).val : K) = (x.val : K)
  rw [PV_Src_ScalarReduce.modulo,cast_mod]

/-- The actual extracted owned matrix refines the field matrix on all raw
U32 input words, including noncanonical words. This is a named source leaf
for the pending external-layer and parent-compression induction. -/
theorem mat4 (x : Array U32 4#usize) :
    ∃ out, AspisBuilderPoseidonReference.poseidon2.builder_reference.mat4_owned x = ok out ∧
      ∀ i : Fin 4, liftU (K := K) out.val[i.val]! =
        R0P.poseidonMat4 (fun j : Fin 4 => liftU x.val[j.val]!) i := by
  obtain ⟨out,run,h0,h1,h2,h3⟩ := R0Z.PoseidonRefine.mat4_lift
    x.val[0]! x.val[1]! x.val[2]! x.val[3]!
    (fun j : Fin 4 => liftU (K := K) x.val[j.val]!) rfl rfl rfl rfl
  refine ⟨out,(PV_Src_ExternalMat4Copy.equals_copy x).trans run,?_⟩
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

#print axioms reduce
#print axioms mat4
end R1Z.PV_RunJoin_SourceArithmeticLift
