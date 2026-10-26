import RPz7_SdkD_PrepareCut
set_option autoImplicit false
noncomputable section
namespace AspisR1.SdkD_PhysicalRoots
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation BorrowedClaimPrepared AspisS1ValuesOwnedInstallation

theorem prepared (ops : Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    {H : Type} (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : H) (p : verifier.Prepared)
    (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (success : verifier.candidate.prepare (RowShape_InstalledSlots.verifierOps ops B std)
      D pub proof hash none input = ok (.Ok p,scratch)) :
    ∃ root0 root1 : Array U8 32#usize,
      p.roots = Array.make 2#usize [root0,root1] ∧
      root0.val = proof.val.slice 16 48 ∧ root1.val = proof.val.slice 63 95 := by
  exact NativeBuffers.prepare_physical_roots (withValues ops) nativeValues
    AspisS1ExtractedRoundChildren.children (ClaimsUnrolledFinish.install std B)
    (fun i o st u h => length_frame i o u st h) D pub proof hash p input scratch success

#print axioms prepared
end AspisR1.SdkD_PhysicalRoots
end
