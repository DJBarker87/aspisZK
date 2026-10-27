import R1Z.PV_Src_PublicDeploymentAssociation
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Src_NativeRootReduced
open Aeneas Aeneas.Std Result R0Z.WriterRefine R1J.SpendWitnessMap
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1 PV_Src_NativeInput
open PV_Src_Forest_PrimitiveArguments
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

/-! Four original source-boundary fields, with the still-open installed public
association passed separately. This is not a deployed 5-to-4 premise removal. -/
structure Core {I : Type} (external : ExternalLinear) (records : Records)
    (inputs : I → Input) (transport : Fin 1024 ≃ Fin 1024) : Prop where
  compile_call : ∀ i, @run external records (inputs i) = ok (.Ok (inputs i).compiled)
  words : ∀ i r, @newRecords records (inputs i) = ok r → WitnessOk (wordWitness r.w)
  admission : ∀ i r, @newRecords records (inputs i) = ok r →
    BuilderSpendRelation.RspendPlus
      (mapPub (K := K) (PV_Src_Public.canonicalPublic (publicInput (inputs i))))
      (BuilderCanonical.liftWitness (BuilderRecordCanonical.witness (wordWitness r.w)))
  row_call : ∀ j, transport j = PV_Src_Transport.row j

theorem toPremises {I : Type} (external : ExternalLinear) (records : Records)
    (inputs : I → Input) (transport : Fin 1024 ≃ Fin 1024)
    (core : Core (K := K) external records inputs transport)
    (association : PV_Src_PublicDeploymentAssociation.Association records inputs) :
    @PV_Src_NativeIdentification.PV_Src_Premises K _ _ _ _ _ external records I inputs transport where
  compile_call := core.compile_call
  words := core.words
  publicCorr := PV_Src_PublicDeploymentAssociation.correspondence records inputs association
  admission := core.admission
  row_call := core.row_call

#print axioms toPremises
end R1Z.PV_Src_NativeRootReduced
