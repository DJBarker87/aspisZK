import R1Z.PV_Src_NativeInput
import R1Z.PV_Src_Forest_Columns
import R1Z.PV_Src_Forest_PrimitiveArguments
import R1Z.PV_Src_Transport

/-! Typed primitive obligations at the actual returned-compiler boundary.
No source-to-model trace equation is hidden in these definitions. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Src_NativeIdentification
open Aeneas Aeneas.Std Result R0P R0Z.ZkStatement R0Z.WriterRefine R1J.SpendWitnessMap
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
open PV_Src_Forest_PrimitiveArguments PV_Src_NativeInput
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]
variable [ExternalLinear] [Records]

def prover {I : Type} (inputs : I → Input) (transport : Fin 1024 ≃ Fin 1024) : HonestProver K where
  Instance := I
  «public» := fun i => mapPub (BuilderPublicProjection.semanticPublic
    (PV_Src_Public.output (publicInput (inputs i))))
  build := fun i => columns PV_Src_Forest_Columns.read (inputs i).compiled.semantic_c1.c1
  transport := transport

/-- Exact remaining facts at the extracted compiler boundary. `compile_call`
retains both error layers; all other record predicates concern the same record
returned by the actual constructor. No output-trace correctness is assumed. -/
structure PV_Src_Premises {I : Type} (inputs : I → Input)
    (transport : Fin 1024 ≃ Fin 1024) : Prop where
  compile_call : ∀ i, run (inputs i) = ok (.Ok (inputs i).compiled)
  words : ∀ i records, newRecords (inputs i) = ok records →
    WitnessOk (wordWitness records.w)
  publicCorr : ∀ i records, newRecords (inputs i) = ok records →
    PubCorr (wordPublic records.p)
      (mapPub (K := K) (PV_Src_Public.canonicalPublic (publicInput (inputs i))))
  admission : ∀ i records, newRecords (inputs i) = ok records →
    BuilderSpendRelation.RspendPlus
      (mapPub (K := K) (PV_Src_Public.canonicalPublic (publicInput (inputs i))))
      (BuilderCanonical.liftWitness (BuilderRecordCanonical.witness (wordWitness records.w)))
  row_call : ∀ j, transport j = PV_Src_Transport.row j

#print PV_Src_Premises
#print axioms prover
end R1Z.PV_Src_NativeIdentification
