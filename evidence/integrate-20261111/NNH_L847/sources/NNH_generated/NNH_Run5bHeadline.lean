import NNH_Run5bHost
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_Run5bHeadline
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open S2W_ReturnedCheckpoint S2W_CommittedCheckpoint S2W_WrapperLaws S2W_D189Consolidation
open NNH_Run5bCtx NNH_Run5bHost
variable {W Tx : Type} (L : Library W (Nat → Record))
 (borrow : S2TrustedSdkBorrow L)
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy)

include borrow
theorem headline : RSL.TAS.Headline (S_host (Tx := Tx) L copy std) where
 deployed := by
  intro c n1 n2 ext ac1 ac2 game queries
  exact RPx_Deployed.deployed L borrow copy std NNE_AbortIndicator.allocator
   c.i.entry c.j.entry c.world.w1 c.world.w2 game.2.1 game.2.2.1
   (missing c) c.fixed.indexError c.fixed.reservation n1 n2 (hashv c) ext
   c.sha256 c.sha256 (DGP_HostDigest.p1 c.sha256) (DGP_HostDigest.syscall c.sha256)
   c.i.data c.j.data c.j.slot true true true true c.world.saved
   (writeBracket c.i.entry.heap 2 0 0 (source (nativeBytes c.world.saved))) c.j.entry.heap
   ac1 ac2 c.fixed.root c.fixed.length c.fixed.prior c.fixed.words
   c.world.p c.world.t c.world.u c.world.actions game.1 game.2.2.2
   c.fixed.D (NNH_StateNormalize.normalize c.fixed.a) c.fixed.Q0 c.fixed.Q1 queries
 numeric := by
  intro c n1 n2 ext queries
  have owners := FJu_GlobalOwners.complete _ _ (FJv_GlobalOwners.complete c.fixed.indexError
   (base c) c.fixed.reservation (FJv_GlobalTerminal.owners (missing c)
    c.fixed.indexError c.fixed.reservation _))
  have security := FJp_Residual.numeric (Tx := Tx) L copy NNE_AbortIndicator.allocator
   (base c) c.fixed.indexError c.fixed.reservation n1 n2 (hashv c) ext
   (NNH_StateNormalize.normalize c.fixed.a) std c.fixed.D c.fixed.words owners
   c.fixed.Q0 c.fixed.Q1 queries
  refine ⟨security,?_,?_⟩
  · intro range
    simpa only [NNH_Run5bHost.runtime, Nat.cast_add] using security.trans (F3U_Range.per_attempt _ range)
  · intro zero
    rw [zero] at security
    exact F3U_Numeric.runtime_margin _ security
#print axioms headline
end AspisR1.NNH_Run5bHeadline
end
