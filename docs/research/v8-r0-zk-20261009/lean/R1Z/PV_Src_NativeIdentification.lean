import R1Z.PV_Src_ForestCompilation
import R1Z.PV_Src_NativePremises
import R1Z.PV_Src_Transport

/-! Source identification for actual returned forest compiler columns. Missing
caller/record facts are named fields, never equations inside the source
prover's definition. No raw-trace equality is a premise. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Src_NativeIdentification
open Aeneas Aeneas.Std Result R0P R0Z.ZkStatement R0Z.WriterRefine R1J.SpendWitnessMap
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
open PV_Src_Forest_PrimitiveArguments PV_Src_NativeInput
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]
variable [ExternalLinear] [Records]

variable {I : Type} {inputs : I → Input} {transport : Fin 1024 ≃ Fin 1024}

theorem existence (p : PV_Src_Premises (K := K) inputs transport) (i : I) :
    ∃ records banks,
      newRecords (inputs i) = ok records ∧
      pair_forest_copy_builder.CopyRecords.banks records = ok (some banks) ∧
      (inputs i).compiled.semantic_c1.c1 = banks.merged :=
  PV_Src_ForestCompilation.returned_bank (inputs i).witness
    (outputValue (inputs i).request) (recipient (inputs i).request) (inputs i).change
    (forestPublic (inputs i).request) (inputs i).laneAnchor (inputs i).snapshot
    (inputs i).compiled (p.compile_call i)

def records (p : PV_Src_Premises (K := K) inputs transport) (i : I) :
    pair_forest_copy_builder.CopyRecords := Classical.choose (existence p i)

theorem record_facts (p : PV_Src_Premises (K := K) inputs transport) (i : I) :
    ∃ banks, newRecords (inputs i) = ok (records p i) ∧
      pair_forest_copy_builder.CopyRecords.banks (records p i) = ok (some banks) ∧
      (inputs i).compiled.semantic_c1.c1 = banks.merged :=
  Classical.choose_spec (existence p i)

def banks (p : PV_Src_Premises (K := K) inputs transport) (i : I) :
    pair_forest_copy_builder.CopyBanks := Classical.choose (record_facts p i)

theorem records_success (p : PV_Src_Premises (K := K) inputs transport) (i : I) :
    newRecords (inputs i) = ok (records p i) := (Classical.choose_spec (record_facts p i)).1

theorem banks_success (p : PV_Src_Premises (K := K) inputs transport) (i : I) :
    pair_forest_copy_builder.CopyRecords.banks (records p i) = ok (some (banks p i)) :=
  (Classical.choose_spec (record_facts p i)).2.1

theorem compiled_columns (p : PV_Src_Premises (K := K) inputs transport) (i : I) :
    (inputs i).compiled.semantic_c1.c1 = (banks p i).merged :=
  (Classical.choose_spec (record_facts p i)).2.2

def toInstance (p : PV_Src_Premises (K := K) inputs transport) (i : I) :
    BuilderCanonical.Instance (K := K) :=
  ⟨(PV_Src_Public.canonicalPublic (publicInput (inputs i)),
      BuilderRecordCanonical.witness (wordWitness (records p i).w)),
    p.admission i (records p i) (records_success p i)⟩

theorem public_eq (p : PV_Src_Premises (K := K) inputs transport) (i : I) :
    (prover inputs transport).public i = BuilderSource.prover.public (toInstance p i) := by
  change mapPub (BuilderPublicProjection.semanticPublic (PV_Src_Public.output _)) = _
  rw [PV_Src_Public.public_eq]
  rfl

theorem build_eq (p : PV_Src_Premises (K := K) inputs transport) (i : I) :
    (prover inputs transport).build i = BuilderSource.prover.build (toInstance p i) := by
  change columns PV_Src_Forest_Columns.read (inputs i).compiled.semantic_c1.c1 =
    BuilderRefinement.mergedTrace
      (BuilderCanonical.rustWitness (BuilderRecordCanonical.witness (wordWitness (records p i).w)))
      (BuilderCanonical.rustPublic (PV_Src_Public.canonicalPublic (publicInput (inputs i))))
  have hc := congrArg (fun out => columns (K := K) PV_Src_Forest_Columns.read out)
    (compiled_columns p i)
  exact hc.trans ((PV_Src_ForestBanks.merged_trace (records p i) (banks p i)
    (banks_success p i)).trans (PV_Src_ForestTrace.canonical_trace _ _ _
      (p.words i _ (records_success p i)) (p.publicCorr i _ (records_success p i))))

theorem transport_eq (p : PV_Src_Premises (K := K) inputs transport) :
    (prover (K := K) inputs transport).transport = BuilderSource.π := by
  apply Equiv.ext
  intro j
  exact (p.row_call j).trans (PV_Src_Transport.row_eq j)

theorem identification (p : PV_Src_Premises (K := K) inputs transport) :
    BuilderSource.SourceIdentification (prover inputs transport) (toInstance p) :=
  ⟨public_eq p,build_eq p,transport_eq p⟩

#print axioms existence
#print axioms records
#print axioms record_facts
#print axioms banks
#print axioms records_success
#print axioms banks_success
#print axioms compiled_columns
#print axioms toInstance
#print axioms public_eq
#print axioms build_eq
#print axioms transport_eq
#print axioms identification
end R1Z.PV_Src_NativeIdentification
