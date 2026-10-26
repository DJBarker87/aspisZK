import R1Z.PV_Src_ForestIdentification
import R1Z.PV_Src_ForestRecords
import R1Z.PV_Src_Canonical

/-! Construct the source certificate for the forest port's own extracted
bank/column pipeline, on the canonical encoding family. Only data carriers
cross namespaces; the source computation is proved in the forest namespace. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Src_ForestCanonical
open Aeneas Aeneas.Std Result R0P R0Z.WriterRefine R1J.SpendWitnessMap
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

abbrev Instance := PV_Src_Canonical.Instance (K := K)

def inputs (i : Instance (K := K)) : PV_Src_ForestIdentification.Input where
  publicInput := (PV_Src_Canonical.inputs i).publicInput
  witnessRecord := PV_Src_ForestRecords.restoreWitness (PV_Src_Canonical.inputs i).witnessRecord
  publicRecord := PV_Src_ForestRecords.restorePublic (PV_Src_Canonical.inputs i).publicRecord

theorem premises : PV_Src_ForestIdentification.PV_Src_Premises
    (K := K) (inputs (K := K)) PV_Src_Transport.transport where
  words := by
    intro i
    change WitnessOk (PV_Src_Forest_PrimitiveArguments.wordWitness
      (PV_Src_ForestRecords.restoreWitness _))
    rw [PV_Src_ForestRecords.word_witness]
    exact PV_Src_Canonical.premises.words i
  publicCorr := by
    intro i
    change PubCorr (PV_Src_Forest_PrimitiveArguments.wordPublic
      (PV_Src_ForestRecords.restorePublic _)) _
    rw [PV_Src_ForestRecords.word_public]
    exact PV_Src_Canonical.premises.publicCorr i
  admission := by
    intro i
    change BuilderSpendRelation.RspendPlus _
      (BuilderCanonical.liftWitness (BuilderRecordCanonical.witness
        (PV_Src_Forest_PrimitiveArguments.wordWitness (PV_Src_ForestRecords.restoreWitness _))))
    rw [PV_Src_ForestRecords.word_witness]
    exact PV_Src_Canonical.premises.admission i
  row_call := fun _ => rfl

theorem identification : BuilderSource.SourceIdentification
    (PV_Src_ForestIdentification.prover (K := K) (inputs (K := K)) PV_Src_Transport.transport)
    (PV_Src_ForestIdentification.toInstance premises) :=
  PV_Src_ForestIdentification.identification premises

theorem canonical_instance (i : Instance (K := K)) :
    PV_Src_ForestIdentification.toInstance premises i = i.canonical := by
  apply Subtype.ext
  change (_,BuilderRecordCanonical.witness
    (PV_Src_Forest_PrimitiveArguments.wordWitness (PV_Src_ForestRecords.restoreWitness _))) = _
  rw [PV_Src_ForestRecords.word_witness]
  change (PV_Src_Public.canonicalPublic (PV_Src_Canonical.inputs i).publicInput,
    BuilderRecordCanonical.witness (BuilderPrimitiveArguments.wordWitness
      (PV_Src_Records.bankWitness (BuilderCanonical.rustWitness i.canonical.val.2)))) = _
  rw [PV_Src_Canonical.encoded_public,PV_Src_Records.witness_roundtrip,
    PV_Src_Records.decoded_witness]

theorem public_eq (i : Instance (K := K)) :
    (PV_Src_ForestIdentification.prover inputs PV_Src_Transport.transport).public i =
      BuilderSource.prover.public i.canonical := by
  exact ((identification (K := K)).public_eq i).trans
    (congrArg (fun p : BuilderCanonical.Instance (K := K) =>
      (BuilderSource.prover (K := K)).public p) (canonical_instance i))

theorem build_eq (i : Instance (K := K)) :
    (PV_Src_ForestIdentification.prover inputs PV_Src_Transport.transport).build i =
      BuilderSource.prover.build i.canonical := by
  exact ((identification (K := K)).build_eq i).trans
    (congrArg (fun p : BuilderCanonical.Instance (K := K) =>
      (BuilderSource.prover (K := K)).build p) (canonical_instance i))

theorem transport_eq :
    (PV_Src_ForestIdentification.prover (K := K) (inputs (K := K)) PV_Src_Transport.transport).transport =
      BuilderSource.π := identification.transport_eq

#print axioms premises
#print axioms identification
#print axioms canonical_instance
#print axioms public_eq
#print axioms build_eq
#print axioms transport_eq
end R1Z.PV_Src_ForestCanonical
