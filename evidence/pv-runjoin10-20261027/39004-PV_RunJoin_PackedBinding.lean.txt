import R1Z.PV_RunJoin_PackedRecords
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PackedBinding
open Aeneas Aeneas.Std Result R1J.SpendWitnessMap
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

theorem projection (i : PV_Src_CheckedCanonical.Data (K := K))
    (bound : i.canonical.val.1.nextPairIndex < 2^64)
    (transition : PV_Src_NativeInput.transition i.compiled.public_statement =
      PV_Src_PublicRecords.transition i.canonical.val.1 bound i.pool i.domain) :
    PV_Src_NativeInput.publicInput (PV_RunJoin_PackedRecords.input i) =
      PV_Src_PublicRecords.input i.canonical.val.1 bound i.pool i.domain i.destination := by
  rw [PV_RunJoin_PackedRecords.input, PV_RunJoin_PackedPublic.packed_public]
  unfold PV_Src_CheckedCanonical.input PV_Src_CheckedEncoding.input
    PV_Src_NativeInput.publicInput PV_Src_CanonicalRequest.request PV_Src_PublicRecords.input
  rw [transition]
  cases i.canonical.val.1.variant <;> rfl

theorem semantic_public (i : PV_Src_CheckedCanonical.Data (K := K))
    (bound : i.canonical.val.1.nextPairIndex < 2^64)
    (transition : PV_Src_NativeInput.transition i.compiled.public_statement =
      PV_Src_PublicRecords.transition i.canonical.val.1 bound i.pool i.domain) :
    PV_Src_Public.canonicalPublic (PV_Src_NativeInput.publicInput (PV_RunJoin_PackedRecords.input i)) =
      i.canonical.val.1 := by
  rw [projection i bound transition]
  exact PV_Src_PublicRecords.public_roundtrip _ _ _ _ _ (PV_Src_OptionShape.canonical i.canonical)

/-- Admission now needs only the explicit compiled-transition association.
Compiler success and deployment installation are still separate obligations. -/
theorem admission (i : PV_Src_CheckedCanonical.Data (K := K))
    (roots : BuilderRecordsReference.Roots)
    (bound : i.canonical.val.1.nextPairIndex < 2^64)
    (transition : PV_Src_NativeInput.transition i.compiled.public_statement =
      PV_Src_PublicRecords.transition i.canonical.val.1 bound i.pool i.domain) :
    BuilderSpendRelation.RspendPlus
      (mapPub (K := K) (PV_Src_Public.canonicalPublic
        (PV_Src_NativeInput.publicInput (PV_RunJoin_PackedRecords.input i))))
      (BuilderCanonical.liftWitness (BuilderRecordCanonical.witness
        (PV_Src_Forest_PrimitiveArguments.wordWitness
          (PV_Src_RecordReference.returned roots (PV_RunJoin_PackedRecords.input i)).w))) :=
  PV_RunJoin_PackedRecords.admission i roots (congrArg (mapPub (K := K)) (semantic_public i bound transition))

#print axioms projection
#print axioms semantic_public
#print axioms admission
end R1Z.PV_RunJoin_PackedBinding
