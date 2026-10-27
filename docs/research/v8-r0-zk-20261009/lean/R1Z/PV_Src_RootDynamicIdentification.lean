import R1Z.PV_Src_RootDynamicPremises
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Src_RootDynamicIdentification
open Aeneas Aeneas.Std Result R1J.SpendWitnessMap
open PV_Src_RootDynamicPremises
local instance : BuilderForestAdmissionPort.ExternalLinear := external
local instance : BuilderForestAdmissionPort.Records := records
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

theorem source {I : Type} (data : I → PV_Src_FrozenInput.Data (K := K))
    (transport : Fin 1024 ≃ Fin 1024) (core : Core data transport) :
    BuilderSource.SourceIdentification
      (PV_Src_NativeIdentification.prover (K := K)
        (fun i => PV_Src_FrozenInput.input (data i)) transport)
      (PV_Src_NativeIdentification.toInstance (PV_Src_RootDynamicPremises.source data transport core)) :=
  PV_Src_NativeIdentification.identification (PV_Src_RootDynamicPremises.source data transport core)

#print axioms source
end R1Z.PV_Src_RootDynamicIdentification
