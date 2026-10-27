import R1Z.PV_RunJoin_UniversalRecords22
import R1Z.PV_RunJoin_UniversalPublic22
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_UniversalBuild22
open Aeneas Aeneas.Std Result R0Z.WriterRefine R1J.SpendWitnessMap
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1 PV_Src_NativeInput
open PV_Src_Forest_PrimitiveArguments
local notation "E" => PV_RunJoin_ShippedExternal.E_shipped
local notation "R" => PV_RunJoin_UniversalRecords22.shipped
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

def records (i : Input) := PV_Src_RecordReference.returned PV_Src_CanonicalRoots.table i

def Admission (i : Input) : Prop := BuilderSpendRelation.RspendPlus
  (mapPub (K := K) (PV_Src_Public.canonicalPublic (publicInput i)))
  (BuilderCanonical.liftWitness (BuilderRecordCanonical.witness (wordWitness (records i).w)))

def toInstance {I : Type} (inputs : I → Input)
    (admitted : ∀ i, Admission (K := K) (inputs i)) (i : I) :
    BuilderCanonical.Instance (K := K) :=
  ⟨(PV_Src_Public.canonicalPublic (publicInput (inputs i)),
    BuilderRecordCanonical.witness (wordWitness (records (inputs i)).w)),admitted i⟩
#print axioms toInstance

/-- This is public_eq at every admitted input, with no compiler-success,
record-success, bank, fixture or selection hypothesis. -/
theorem public_eq {I : Type} (inputs : I → Input)
    (transport : Fin 1024 ≃ Fin 1024) (admitted : ∀ i, Admission (K := K) (inputs i)) :
    ∀ i, (PV_Src_NativeIdentification.prover (K := K) inputs transport).public i =
      BuilderSource.prover.public (toInstance inputs admitted i) :=
  PV_RunJoin_UniversalPublic22.public_eq inputs transport (toInstance inputs admitted) (fun _ => rfl)
#print axioms public_eq

/-- The universal successful compiler law selects the same record and bank.
No per-fixture compiler payload is substituted. -/
theorem returned_bank (i : Input) (success : @run E R i = ok (.Ok i.compiled)) :
    ∃ banks, pair_forest_copy_builder.CopyRecords.banks (records i) = ok (some banks) ∧
      i.compiled.semantic_c1.c1 = banks.merged := by
  obtain ⟨r,banks,hr,hb,hc⟩ := @PV_Src_ForestCompilation.returned_bank E R i.witness
    (outputValue i.request) (recipient i.request) i.change (forestPublic i.request)
    i.laneAnchor i.snapshot i.compiled success
  have he := PV_RunJoin_UniversalRecords22.returned i r hr
  subst r
  exact ⟨banks,hb,hc⟩
#print axioms returned_bank

theorem build_eq {I : Type} (inputs : I → Input)
    (transport : Fin 1024 ≃ Fin 1024) (admitted : ∀ i, Admission (K := K) (inputs i))
    (success : ∀ i, @run E R (inputs i) = ok (.Ok (inputs i).compiled))
    (checked : ∀ i, PV_Src_RecordReference.Checked (inputs i))
    (frontier : ∀ i (l : Fin 20), Canon8 (inputs i).snapshot.frontier.val[l.val]!) :
    ∀ i, (PV_Src_NativeIdentification.prover (K := K) inputs transport).build i =
      BuilderSource.prover.build (toInstance inputs admitted i) := by
  intro i
  obtain ⟨banks,hb,hc⟩ := returned_bank (inputs i) (success i)
  change columns PV_Src_Forest_Columns.read (inputs i).compiled.semantic_c1.c1 = _
  rw [hc]
  exact (PV_Src_ForestBanks.merged_trace (records (inputs i)) banks hb).trans
    (PV_Src_ForestTrace.canonical_trace _ _ _
      (PV_RunJoin_UniversalRecords22.words (inputs i) (checked i) _
        (PV_RunJoin_UniversalRecords22.newRecords (inputs i)))
      (PV_RunJoin_UniversalRecords22.publicCorr (inputs i) (success i) (frontier i) _
        (PV_RunJoin_UniversalRecords22.newRecords (inputs i))))
#print axioms build_eq

/-- Transport identification for the extracted reference, at every index. -/
theorem transport_eq {I : Type} (inputs : I → Input) :
    (PV_Src_NativeIdentification.prover (K := K) inputs PV_Src_Transport.transport).transport =
      BuilderSource.π := PV_Src_Transport.transport_eq
#print axioms transport_eq

/-- Exact SourceIdentification assembly; the unresolved universal compiler
success/admission and primitive word guards remain visibly quantified. -/
theorem identification {I : Type} (inputs : I → Input)
    (admitted : ∀ i, Admission (K := K) (inputs i))
    (success : ∀ i, @run E R (inputs i) = ok (.Ok (inputs i).compiled))
    (checked : ∀ i, PV_Src_RecordReference.Checked (inputs i))
    (frontier : ∀ i (l : Fin 20), Canon8 (inputs i).snapshot.frontier.val[l.val]!) :
    BuilderSource.SourceIdentification
      (PV_Src_NativeIdentification.prover (K := K) inputs PV_Src_Transport.transport)
      (toInstance inputs admitted) :=
  ⟨public_eq inputs _ admitted,build_eq inputs _ admitted success checked frontier,transport_eq inputs⟩
#print axioms identification
end R1Z.PV_RunJoin_UniversalBuild22
