import S1CurrentOwnedConcreteJoinV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS1PreparedActiveBoundaries
open AspisR1PublicPreparation

theorem prepare_eq_of_active (first second : PreparedScratchModel.Boundaries)
    (bytes : first.sampling.toBytes=second.sampling.toBytes)
    (fromQm : first.sampling.fromQm=second.sampling.fromQm)
    (ordinary : first.sampling.ordinary=second.sampling.ordinary)
    (gamma : first.sampling.gamma=second.sampling.gamma)
    (queries : @PreparedModel.Boundaries.queries first.sampling=@PreparedModel.Boundaries.queries second.sampling)
    (powers : first.powers=second.powers)
    (claim : @PreparedScratchModel.Boundaries.claim first=@PreparedScratchModel.Boundaries.claim second) :
    @PreparedScratchModel.prepare first=@PreparedScratchModel.prepare second := by
  funext H digest sem view hash scratch
  unfold PreparedScratchModel.prepare PreparedModel.scalar PreparedModel.scalar_k
  simp only [bytes,fromQm,ordinary,gamma,queries,powers,claim]

/-- Every actually used sampling field is concretely installed. The retained
legacy claim field is never invoked by PreparedScratchModel.prepare. -/
theorem concrete_sampling_irrelevant (first second : PreparedModel.Boundaries) :
    @PreparedScratchModel.prepare
      (AspisR1ClaimPreparedBridge.concreteBoundaries
        (AspisR1ClaimPreparedBridge.InstalledMeaning.installedBoundaries
          (AspisR1CurrentCaller.OriginalSerializerInstallation.withOriginalSerializer first)
          AspisS1M31Embedding.Total.embed)) =
    @PreparedScratchModel.prepare
      (AspisR1ClaimPreparedBridge.concreteBoundaries
        (AspisR1ClaimPreparedBridge.InstalledMeaning.installedBoundaries
          (AspisR1CurrentCaller.OriginalSerializerInstallation.withOriginalSerializer second)
          AspisS1M31Embedding.Total.embed)) := by
  apply prepare_eq_of_active <;> rfl

#print axioms prepare_eq_of_active
#print axioms concrete_sampling_irrelevant
end AspisS1PreparedActiveBoundaries
