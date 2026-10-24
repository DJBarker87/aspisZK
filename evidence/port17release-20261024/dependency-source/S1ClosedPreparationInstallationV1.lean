import S1PreparedActiveBoundariesV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
noncomputable section
namespace AspisR1CurrentCaller.BorrowedClaimPrepared
open AspisR1CurrentCaller AspisR1ClaimPreparedBridge
open OriginalSerializerInstallation

/-- Fully defined legacy operation, retained for the complete original record.
The scratch preparation model never invokes this legacy field. -/
def legacyReference {H : Type} (digest : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (sem : AspisR1PublicPreparation.r1_semantic.Verified H) (bytes : Slice U8)
    (inactive gamma kappa : PE) :
    Result (core.result.Result PE AspisR1PublicPreparation.verifier.Error) := do
  let powers ← powersPublic 29#usize gamma
  claimPublic digest sem bytes inactive powers kappa

/-- All fields are concrete existing procedures; no arbitrary sampler/embed/
serializer function or inert replacement carrier supplies this record. -/
def closedSampling : AspisR1PublicPreparation.PreparedModel.Boundaries where
  toBytes := sourceBytes
  fromQm := AspisR1PublicPreparation.PreparedFromQmSourceBridge.fromQmSource
  ordinary := AspisR1Post25SamplerOrdinaryCallbackV2.candidateOrdinaryPublic
  gamma := candidateGammaPublic
  queries := fun digest transcript row payload =>
    AspisR1PublicPreparation.QueriesModel.queries
      (Query31ConcreteMaterializedSchedule.concreteBoundaries
        Query31ConcreteDriverTraceFacts.sourceDefaultState AspisS1M31Embedding.Total.embed)
      digest transcript row payload
  claim := legacyReference

/-- Full Result and the same returned scratch, on every input. The seed record
has no effect once all active source children are installed. -/
theorem originalNew_sampling_irrelevant
    (first second : AspisR1PublicPreparation.PreparedModel.Boundaries) :
    @originalNew (withOriginalSerializer first) AspisS1M31Embedding.Total.embed =
    @originalNew (withOriginalSerializer second) AspisS1M31Embedding.Total.embed := by
  funext H digest sem view hash scratch
  rw [originalNew_eq_transport,originalNew_eq_transport]
  rw [AspisS1PreparedActiveBoundaries.concrete_sampling_irrelevant first second]

theorem concreteInstall_irrelevant (ops : Ops)
    (first second : AspisR1PublicPreparation.PreparedModel.Boundaries) :
    concreteInstall ops first=concreteInstall ops second := by
  unfold concreteInstall install
  rw [originalNew_sampling_irrelevant first second]

def closedInstall (ops : Ops) : Ops := concreteInstall ops closedSampling

theorem closedInstall_eq (ops : Ops) (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries) :
    closedInstall ops=concreteInstall ops sampling := concreteInstall_irrelevant ops closedSampling sampling

def closedCallerDigest (adapterOps : AdapterRw.Ops) (ops : Ops) : aspis_core.digest.Digest32 Unit :=
  concreteCallerDigest adapterOps ops closedSampling

#print axioms legacyReference
#print axioms closedSampling
#print axioms originalNew_sampling_irrelevant
#print axioms concreteInstall_irrelevant
#print axioms closedInstall_eq
end AspisR1CurrentCaller.BorrowedClaimPrepared
