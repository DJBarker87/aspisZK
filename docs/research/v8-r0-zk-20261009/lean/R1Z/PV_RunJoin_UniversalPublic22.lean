import R1Z.PV_Src_NativePremises
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_UniversalPublic22
open R1J.SpendWitnessMap
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

/-- Public projection holds on every native data input, including rejected
compilations. This is the native canonical projection, not yet an equation
identifying an independently supplied canonical spend instance. -/
theorem projection {I : Type} (inputs : I → PV_Src_NativeInput.Input)
    (transport : Fin 1024 ≃ Fin 1024) (i : I) :
    (PV_Src_NativeIdentification.prover (K := K) inputs transport).public i =
      mapPub (K := K) (PV_Src_Public.canonicalPublic
        (PV_Src_NativeInput.publicInput (inputs i))) := by
  change mapPub (BuilderPublicProjection.semanticPublic (PV_Src_Public.output _)) = _
  rw [PV_Src_Public.public_eq]
#print axioms projection

/-- An independently admitted instance requires only the public association
for this field. Compiler success, words and bank validation play no part in
public_eq, and are not silently inserted as hypotheses here. -/
theorem public_eq {I : Type} (inputs : I → PV_Src_NativeInput.Input)
    (transport : Fin 1024 ≃ Fin 1024)
    (toInstance : I → BuilderCanonical.Instance (K := K))
    (association : ∀ i, PV_Src_Public.canonicalPublic
      (PV_Src_NativeInput.publicInput (inputs i)) = (toInstance i).val.1) :
    ∀ i, (PV_Src_NativeIdentification.prover (K := K) inputs transport).public i =
      BuilderSource.prover.public (toInstance i) := by
  intro i
  rw [projection inputs transport i,association i]
  rfl
#print axioms public_eq
end R1Z.PV_RunJoin_UniversalPublic22
