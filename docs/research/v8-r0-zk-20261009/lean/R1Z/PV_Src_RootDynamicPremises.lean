import R1Z.PV_Src_RootDynamicPublicStages
import R1Z.PV_Src_NativeIdentification
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Src_RootDynamicPremises
open Aeneas Aeneas.Std Result R0Z.WriterRefine R1J.SpendWitnessMap
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1 PV_Src_NativeInput
open PV_Src_Forest_PrimitiveArguments
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

abbrev external := PV_Src_ExternalReference.dictionary
abbrev records := @PV_Src_RecordDynamic.dictionary external
local instance : ExternalLinear := external
local instance : Records := records

/-! Three remaining obligations for the computed-root source dictionary on
canonical encoded data. Installed input/mapper association is still separate. -/
structure Core {I : Type} (data : I → PV_Src_FrozenInput.Data (K := K))
    (transport : Fin 1024 ≃ Fin 1024) : Prop where
  compile_call : ∀ i, @run external records (PV_Src_FrozenInput.input (data i)) =
    ok (.Ok (PV_Src_FrozenInput.input (data i)).compiled)
  admission : ∀ i r, @newRecords records (PV_Src_FrozenInput.input (data i)) = ok r →
    BuilderSpendRelation.RspendPlus
      (mapPub (K := K) (PV_Src_Public.canonicalPublic (publicInput (PV_Src_FrozenInput.input (data i)))))
      (BuilderCanonical.liftWitness (BuilderRecordCanonical.witness (wordWitness r.w)))
  row_call : ∀ j, transport j = PV_Src_Transport.row j

theorem source {I : Type} (data : I → PV_Src_FrozenInput.Data (K := K))
    (transport : Fin 1024 ≃ Fin 1024) (core : Core data transport) :
    @PV_Src_NativeIdentification.PV_Src_Premises K _ _ external records I
      (fun i => PV_Src_FrozenInput.input (data i)) transport where
  compile_call := core.compile_call
  words := fun i r hr => @PV_Src_RecordDynamic.words external _ (PV_Src_FrozenInput.checked (data i)) r hr
  publicCorr := fun i r hr => PV_Src_PublicRootClosed.correspondence _ (core.compile_call i)
    (PV_Src_FrozenInput.frontier (data i)) r hr
  admission := core.admission
  row_call := core.row_call

#print axioms source
end R1Z.PV_Src_RootDynamicPremises
