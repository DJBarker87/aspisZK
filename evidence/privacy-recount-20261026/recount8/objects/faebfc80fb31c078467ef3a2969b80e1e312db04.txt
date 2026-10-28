import R1Z.PV_Join_PublicDataIff
import R1Z.PV_Join_FixtureInputs
import R1Z.ProverRw19MathematicalAssembly
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_FixtureData
open Aeneas Aeneas.Std Result ProverRwFull ProverRwBodyDataCriterion

/-- Exact source-record criterion for the independent serialization model.
The protocol-to-fields/queries/slots map, actual compiler association and
right-hand byte equation are all still open. The source output never defines
any mathematical model argument. -/
theorem criterion (base : ExternalTypes)
    (ops : @ExternalFuns (PV_Join_PublicCaller.native base)) :
    letI : ExternalTypes := PV_Join_PublicCaller.native base
    ∀ {S : Type} (store : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore S)
    (i : PV_Src_NativeInput.Input)
    (v : transport.Variant) (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (binding digest : Array U8 32#usize)
    (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets)
    (s after : S) (accepted : Bool)
    (reservation : store.«reserve» s digest attempt.mask_nonce = ok (accepted,after))
    (fields : ProverCommitFront46.Fields)
    (queries : List ProverCommitPublish43.QueryParts)
    (slots : List ProverCommitPublish43.Slot),
    PV_Join_PublicCaller.execute base ops store
      (PV_Join_FixtureInputs.publicInput base i)
      (PV_Join_FixtureInputs.compiled base i.compiled)
      v hash binding digest attempt s =
      ProverRwBodyCandidateData.withState after
        (ProverRw19MathematicalAssembly.output fields queries slots) ↔
    PV_RW_DataProduct.observe PV_RW_DataProduct.first
      (data (PV_Join_PublicCaller.execute base ops store
        (PV_Join_FixtureInputs.publicInput base i)
        (PV_Join_FixtureInputs.compiled base i.compiled)
        v hash binding digest attempt s)) =
      ProverRw19MathematicalAssembly.proofBytes fields queries slots := by
  letI : ExternalTypes := PV_Join_PublicCaller.native base
  intro S store i v hash binding digest attempt s after accepted reservation fields queries slots
  exact PV_Join_PublicDataIff.criterion base ops store _ _ v hash binding digest
    attempt s after accepted reservation (ProverRw19MathematicalAssembly.proofBytes fields queries slots)

#print axioms criterion
end R1Z.PV_Join_FixtureData
