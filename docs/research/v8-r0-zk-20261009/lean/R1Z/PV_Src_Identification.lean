import R1Z.PV_Src_Public
import R1Z.PV_Src_Trace
import R1Z.PV_Src_Transport

/-! Source identification for the actual extracted public/bank/column stages.
The still missing record/admission facts are named premises. This module
makes no claim that a forest entry point has supplied them. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Src_Identification
open Aeneas Aeneas.Std Result R0P R0Z.WriterRefine R0Z.ZkStatement
open BuilderPrimitiveArguments R1J.SpendWitnessMap
open AspisBuilderGlueSource.pool_v1.pair_forest_copy_builder
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

structure Input where
  publicInput : PV_Src_Public.Input
  witnessRecord : RW
  publicRecord : RP

/-- Data only: actual extracted public and trace computations. No equality,
canonical membership, success or builder-soundness proposition defines it. -/
def prover {I : Type} (inputs : I → Input) (transport : Fin 1024 ≃ Fin 1024) : HonestProver K where
  Instance := I
  «public» := fun i => mapPub (BuilderPublicProjection.semanticPublic
    (PV_Src_Public.output (inputs i).publicInput))
  build := fun i => PV_Src_Trace.trace (inputs i).witnessRecord (inputs i).publicRecord
  transport := transport

/-- Each remaining source fact is explicit. `admission` is the adopted
RspendPlus including the transfer change sentinel, not trace validity. -/
structure PV_Src_Premises {I : Type} (inputs : I → Input)
    (transport : Fin 1024 ≃ Fin 1024) : Prop where
  words : ∀ i, WitnessOk (wordWitness (inputs i).witnessRecord)
  publicCorr : ∀ i, PubCorr (wordPublic (inputs i).publicRecord)
    (mapPub (K := K) (PV_Src_Public.canonicalPublic (inputs i).publicInput))
  admission : ∀ i, BuilderSpendRelation.RspendPlus
    (mapPub (K := K) (PV_Src_Public.canonicalPublic (inputs i).publicInput))
    (BuilderCanonical.liftWitness (BuilderRecordCanonical.witness (wordWitness (inputs i).witnessRecord)))
  row_call : ∀ j, transport j = PV_Src_Transport.row j

variable {I : Type} {inputs : I → Input} {transport : Fin 1024 ≃ Fin 1024}

def toInstance (premises : PV_Src_Premises (K := K) inputs transport) (i : I) :
    BuilderCanonical.Instance (K := K) :=
  ⟨(PV_Src_Public.canonicalPublic (inputs i).publicInput,
    BuilderRecordCanonical.witness (wordWitness (inputs i).witnessRecord)),premises.admission i⟩

theorem public_eq (premises : PV_Src_Premises (K := K) inputs transport) (i : I) :
    (prover inputs transport).public i = BuilderSource.prover.public (toInstance premises i) := by
  change mapPub (BuilderPublicProjection.semanticPublic (PV_Src_Public.output _)) = _
  rw [PV_Src_Public.public_eq]
  rfl

theorem build_eq (premises : PV_Src_Premises (K := K) inputs transport) (i : I) :
    (prover inputs transport).build i = BuilderSource.prover.build (toInstance premises i) :=
  PV_Src_Trace.canonical_trace _ _ _ (premises.words i) (premises.publicCorr i)

theorem transport_eq (premises : PV_Src_Premises (K := K) inputs transport) :
    (prover (K := K) inputs transport).transport = BuilderSource.π := by
  apply Equiv.ext
  intro j
  exact (premises.row_call j).trans (PV_Src_Transport.row_eq j)

def identification (premises : PV_Src_Premises (K := K) inputs transport) :
    BuilderSource.SourceIdentification (prover inputs transport) (toInstance premises) :=
  ⟨public_eq premises,build_eq premises,transport_eq premises⟩

theorem builderSoundOn {CommitHandle : Type}
    (hcard : 4096 < Fintype.card K) (Fbase : Subfield K) (B : PackBasis Fbase)
    (x : Statement K CommitHandle) (premises : PV_Src_Premises (K := K) inputs transport) :
    R0Z.HonestValidity.BuilderSoundOn (prover inputs transport) B x :=
  BuilderSource.builder_refinement_D46_D51 hcard Fbase B x _ _ (identification premises)

#print axioms toInstance
#print axioms public_eq
#print axioms build_eq
#print axioms transport_eq
#print axioms identification
#print axioms builderSoundOn
end R1Z.PV_Src_Identification
