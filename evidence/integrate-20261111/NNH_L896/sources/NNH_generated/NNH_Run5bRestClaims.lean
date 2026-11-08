import NNH_Run5bSplit
import NNH_Run5bHeadline
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_Run5bRestClaims
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open S2W_ReturnedCheckpoint S2W_CommittedCheckpoint S2W_WrapperLaws S2W_D189Consolidation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open NNH_Run5bCtx NNH_Run5bHost
variable {W Tx : Type} (L : Library W (Nat → Record))
 (borrow : S2TrustedSdkBorrow L)
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy)
include borrow

def Goal (ctx : Ctx W Tx) (native1 : S2W_ExtractionBoundary.First)
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
    (F3X_ModelClaims.Claims (FIp_Install.configuration indexError c reservation) D P (Q0+Q1) ∧
      F3Y_SourceClaims.Claims (FIp_Install.configuration indexError c reservation) D hashv P (Q0+Q1) select ∧
      F3Y_AccountMass.Claims (FIp_Install.configuration indexError c reservation) hashv P (Q0+Q1) select ∧
      F3T_RuntimeBound.failureModel runtime ≤ F3T_Numeric.total (Q0+Q1) ∧
      (Q0+Q1 ≤ F3U_RangeEdges.maxQueries →
        F3T_RuntimeBound.failureModel runtime ≤ (Q0+Q1+1:Rat)*(1/(2:Rat)^100)) ∧
      (Q0+Q1=0 → F3U_Numeric.margin ≤ 1/(2:Rat)^100-F3T_RuntimeBound.failureModel runtime ∧
        F3T_RuntimeBound.failureModel runtime < 1/(2:Rat)^100))

theorem produce (c : Ctx W Tx) (n1 : S2W_ExtractionBoundary.First)
 (n2 : S2W_ExtractionBoundary.Second)
 (ext : (S_host L copy std).Extraction c n1 n2)
 (ac1 : (S_host L copy std).Accepted1 c n1)
 (game : (S_host L copy std).Game c n1 n2)
 (queries : (S_host L copy std).Queries c n1) :
 Goal L copy c n1 n2 := by
 let cfg := configuration c
 let a := NNH_StateNormalize.normalize c.fixed.a
 let prover := ARW_Induced.program n1 copy NNE_AbortIndicator.allocator CPH_Program.verifier a
 let select : F3X_Projection.Output → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs :=
  fun _ => P2P_NativeSelection.pair (sdk c) CPH_Program.verifier c.i.entry c.j.entry c.j.data c.j.slot
 have q : ∀ H, (eval H prover).1.length ≤ c.fixed.Q0+c.fixed.Q1 := by
  intro H
  rw [ARW_Induced.queries]
  exact queries H
 let selected := FIp_Install.select c.fixed.reservation (base c)
 let core := Rc2_Install.configuration (Rc5_Install.seed c.fixed.indexError selected) c.fixed.reservation
 have owners := FJu_GlobalOwners.complete _ _ (FJv_GlobalOwners.complete c.fixed.indexError
  (base c) c.fixed.reservation (FJv_GlobalTerminal.owners (missing c)
   c.fixed.indexError c.fixed.reservation _))
 have cost := FJp_Cost.source_cost core (FIo_Install.finishOps c.fixed.reservation (base c).finish)
  (FIo_Nonvacuity.arithmetic_fixed c.fixed.reservation (base c).finish).symm
  ⟨rfl,rfl,rfl⟩ (hashv c) c.fixed.D c.fixed.words prover (c.fixed.Q0+c.fixed.Q1) q select
  (F3Y_InstalledLaws.prepare c.fixed.indexError selected c.fixed.reservation)
  (F3Y_InstalledLaws.primitives c.fixed.indexError selected c.fixed.reservation)
  (F3Y_InstalledLaws.canonical c.fixed.indexError selected c.fixed.reservation)
  (F3Y_InstalledLaws.domain c.fixed.indexError selected c.fixed.reservation)
  (F3Y_InstalledLaws.multiply c.fixed.indexError selected c.fixed.reservation)
  (F3Y_InstalledLaws.one c.fixed.indexError selected c.fixed.reservation)
  (F3Y_InstalledLaws.inverse c.fixed.indexError selected c.fixed.reservation)
  owners (FJp_MatchingLaw.value c.fixed.indexError (base c) c.fixed.reservation _)
 have mass := F3Y_AccountMass.claims core (hashv c) c.fixed.D c.fixed.words prover
  (c.fixed.Q0+c.fixed.Q1) q select
 have numeric := (NNH_Run5bHeadline.headline L borrow copy std).numeric c n1 n2 ext queries
 exact ⟨F3X_ModelClaims.claims _ c.fixed.D prover _ q,cost,mass,numeric.1,numeric.2⟩
#print axioms Goal
#print axioms produce
end AspisR1.NNH_Run5bRestClaims
end
