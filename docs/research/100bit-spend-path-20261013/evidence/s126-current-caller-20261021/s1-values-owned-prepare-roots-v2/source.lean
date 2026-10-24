import S1NativePreparePhysicalRootsV1
import S1ValuesOwnedInstallationV1
set_option autoImplicit false
namespace AspisS1ValuesOwnedInstallation
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller AspisR1CurrentCaller.BorrowedClaimPrepared

/-- The complete owned-reference installation removes the value-length premise
from this enclosing caller theorem. Native/reference transport over the reached
format domain and SDK/account correspondence remain separate obligations. -/
theorem prepare_physical_roots (ops : Ops)
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    {H : Type} (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : H) (prepared : verifier.Prepared)
    (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (success : verifier.candidate.prepare (NativeBuffers.install (withValues ops) nativeValues R B)
      D pub proof hash none input=ok (.Ok prepared,scratch)) :
    ∃ (root0 root1 : Array U8 32#usize),
      prepared.roots=Array.make 2#usize [root0,root1] ∧
      root0.val=proof.val.slice 16 48 ∧ root1.val=proof.val.slice 63 95 := by
  exact NativeBuffers.prepare_physical_roots (AspisS1ValuesOwnedInstallation.withValues ops) AspisS1ValuesOwnedInstallation.nativeValues R B (fun i o s u h => AspisS1ValuesOwnedInstallation.length_frame i o u s h) D pub proof hash prepared input scratch success

#print axioms prepare_physical_roots
end AspisS1ValuesOwnedInstallation
