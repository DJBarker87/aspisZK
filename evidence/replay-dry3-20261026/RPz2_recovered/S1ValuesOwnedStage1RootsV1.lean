import S1NativeOwnedStage1PhysicalRootsV1
import S1ValuesOwnedInstallationV1
set_option autoImplicit false
namespace AspisS1ValuesOwnedInstallation
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller AspisR1CurrentCaller.BorrowedClaimPrepared

/-- The complete owned-reference installation removes the value-length premise
from this enclosing caller theorem. Native/reference transport over the reached
format domain and SDK/account correspondence remain separate obligations. -/
theorem owned_stage1_physical_roots (adapterOps : AdapterRw.Ops) (ops : Ops)
   
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (program : AdapterRw.solana_pubkey.Pubkey)
    (accounts : Slice AdapterRw.r1_pool_adapter.owned.OwnedAccount)
    (data : Slice U8) (out : alloc.vec.Vec U8)
    (accepted : AdapterRw.r1_pool_adapter.owned.stage1_owned
      (AspisS6CurrentFirstInstallation.install adapterOps (NativeBuffers.install (withValues ops) nativeValues R B))
      program accounts data=ok (.Ok out)) :
    ∃ (bytes proof : Slice U8) (split : Usize)
      (statement : AspisR1PublicPreparation.FirstCaller.DecoderStatement),
      AspisR1PublicPreparation.S6DecoderScopedReuseV1.decodeActual bytes=ok (.Ok statement) ∧
      split=compact.SPLIT ∧
      ∃ (zero : aspis_core.field.wide_exact.WideExact) (prepared : verifier.Prepared)
        (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
        (root0 root1 : Array U8 32#usize),
        verifier.candidate.prepare (NativeBuffers.install (withValues ops) nativeValues R B) (NativeBuffers.callerDigest adapterOps (withValues ops) nativeValues R B)
          (FirstComposition.toCurrentPublic
            (AspisR1PublicPreparation.PreparationBinding.preparationPublic statement))
          proof () none (Array.repeat 29#usize zero)=ok (.Ok prepared,scratch) ∧
        prepared.roots=Array.make 2#usize [root0,root1] ∧ root0.val=proof.val.slice 16 48 ∧ root1.val=proof.val.slice 63 95 ∧
        Tx1Reachability.afterPrepare (NativeBuffers.install (withValues ops) nativeValues R B) (NativeBuffers.callerDigest adapterOps (withValues ops) nativeValues R B)
          bytes proof split () none prepared scratch=ok (.Ok out) := by
  exact NativeBuffers.owned_stage1_physical_roots adapterOps (AspisS1ValuesOwnedInstallation.withValues ops) AspisS1ValuesOwnedInstallation.nativeValues R B (fun i o s u h => AspisS1ValuesOwnedInstallation.length_frame i o u s h) program accounts data out accepted

#print axioms owned_stage1_physical_roots
end AspisS1ValuesOwnedInstallation
