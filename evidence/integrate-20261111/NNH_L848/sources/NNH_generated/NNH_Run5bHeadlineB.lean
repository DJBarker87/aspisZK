import NNH_Run5bHeadline
import NNH_Run5bExec
import NNH_OutcomeRecAccepted
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_Run5bHeadlineB
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open S2W_ReturnedCheckpoint S2W_CommittedCheckpoint S2W_WrapperLaws S2W_D189Consolidation
open NNH_Run5bCtx NNH_Run5bHost
open AspisV8R19.MemoizedProgramLaw
open NNH_Run5bExec FS FS2 MultiproofConeCanonical
variable {W Tx : Type} (L : Library W (Nat → Record))
 (borrow : S2TrustedSdkBorrow L)
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy)

def outcomeRec (ctx : Ctx W Tx) (native1 : S2W_ExtractionBoundary.First)
 (native2 : S2W_ExtractionBoundary.Second) : Prop :=
 let c := base ctx
 let indexError := ctx.fixed.indexError
 let reservation := ctx.fixed.reservation
 let allocator := NNE_AbortIndicator.allocator
 let e1 := ctx.i.entry
 let e2 := ctx.j.entry
 let w1 := ctx.world.w1
 let w2 := ctx.world.w2
 let data1 := ctx.i.data
 let data2 := ctx.j.data
 let slot := ctx.j.slot
 let saved := ctx.world.saved
 let post1 := writeBracket ctx.i.entry.heap 2 0 0 (source (nativeBytes ctx.world.saved))
 let post2 := ctx.j.entry.heap
 let hashv := hashv ctx
 let H := ctx.sha256
 let prior := ctx.fixed.prior
 let p := ctx.world.p
 let t := ctx.world.t
 let u := ctx.world.u
 let D := ctx.fixed.D
 let a := NNH_StateNormalize.normalize ctx.fixed.a
 let Q0 := ctx.fixed.Q0
 let Q1 := ctx.fixed.Q1
    let P := ARW_Induced.program native1 copy allocator CPH_Program.verifier a;
    let runtime := ARX_AdmittedRuntime.runtime (Tx := Tx) L copy allocator c indexError reservation native1 native2 hashv a;
    let select : F3X_Projection.Output → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs :=
      fun _ => P2P_NativeSelection.pair
        (DrvC_Installation.sdk (FIp_Install.configuration indexError c reservation))
        CPH_Program.verifier e1 e2 data2 slot;
    (FJv_DResult.Outcome L e1 e2 w1 w2
      (FIp_Install.configuration indexError c reservation).adapter (FIp_Install.configuration indexError c reservation).currentBase
      (FIp_Install.configuration indexError c reservation).reserved (FIp_Install.configuration indexError c reservation).query
      (FIp_Install.configuration indexError c reservation).geometry (FIp_Install.configuration indexError c reservation).stageBase
      (FIp_Install.configuration indexError c reservation).finish (FIp_Install.boundaries c.boundaries)
      reservation CPH_Program.verifier data1 data2 slot saved post1 post2 H
      (DrvC_Implementation.driver (FIp_Install.configuration indexError c reservation)) prior
      (p.physicalEvents t) hashv
      ((NNH_Run5bExec.recSig L copy std).EventRec ctx))

include borrow
def headlineB : RSL.EVB.HeadlineB (S_host (Tx := Tx) L copy std) (recSig L copy std) where
 OutcomeRec := outcomeRec L copy std
 outcomeRec := by
  intro c n1 n2 ext ac1 ac2 game queries selects
  have budget : ∀ H, firstReads emptyTable (eval H
   (NNH_RecordedCharge.source copy (base c) c.fixed.indexError c.fixed.reservation
    (hashv c) c.fixed.a (c.fixed.Q0+c.fixed.Q1))).1 ≤ c.fixed.Q0+c.fixed.Q1+1921 := by
   intro H
   exact (VerifierCallBudget.firstReads_le_length _ _).trans (ARX_LocalCharge.budget _ _ H)
  exact NNH_OutcomeRecAccepted.accepted L borrow copy std NNE_AbortIndicator.allocator
   c.i.entry c.j.entry c.world.w1 c.world.w2 game.2.1 game.2.2.1
   (missing c) c.fixed.indexError c.fixed.reservation n1 n2 (hashv c) ext
   c.sha256 c.sha256 (DGP_HostDigest.p1 c.sha256) (DGP_HostDigest.syscall c.sha256)
   c.i.data c.j.data c.j.slot true true true true c.world.saved
   (writeBracket c.i.entry.heap 2 0 0 (source (nativeBytes c.world.saved))) c.j.entry.heap
   ac1 ac2 c.fixed.root c.fixed.length c.fixed.prior c.fixed.words
   c.world.p c.world.t c.world.u c.world.actions game.1 game.2.2.2
   c.fixed.D (NNH_StateNormalize.normalize c.fixed.a) c.fixed.Q0 c.fixed.Q1 queries
   (NNH_RecordedCharge.source copy (base c) c.fixed.indexError c.fixed.reservation
    (hashv c) c.fixed.a (c.fixed.Q0+c.fixed.Q1))
   ARQ_Observer.project (ARQ_Observer.select (configuration c) CPH_Program.verifier)
   (c.fixed.Q0+c.fixed.Q1) budget selects
#print axioms headlineB
end AspisR1.NNH_Run5bHeadlineB
end
