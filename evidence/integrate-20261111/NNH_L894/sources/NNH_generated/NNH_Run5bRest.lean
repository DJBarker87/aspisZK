import NNH_Run5bSplit
import NNH_Run5bHeadline
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_Run5bRest
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

theorem rest (c : Ctx W Tx) (n1 : S2W_ExtractionBoundary.First)
 (n2 : S2W_ExtractionBoundary.Second)
 (ext : (S_host L copy std).Extraction c n1 n2)
 (ac1 : (S_host L copy std).Accepted1 c n1)
 (game : (S_host L copy std).Game c n1 n2)
 (queries : (S_host L copy std).Queries c n1) :
 NNH_Run5bSplit.rest L copy c n1 n2 := by
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
 refine ⟨P6C_Extension.boundary (hashv c) c.sha256 c.sha256
   (DGP_HostDigest.p1 c.sha256) (DGP_HostDigest.syscall c.sha256),
  DrvC_SourceEntry.same_program _ (hashv c),DrvC_Installation.aus1_dictionary _,
  ⟨F3X_ModelClaims.claims _ c.fixed.D prover _ q,cost,mass,numeric.1,numeric.2⟩,
  ?_,?_,?_,?_,?_,S6N_Installation.facts cfg⟩
 · exact PoolT_Write.accepted_verifier_writes_copy (sdk c) n1 n2 (hashv c) ext copy std
    NNE_AbortIndicator.allocator c.i.entry CPH_Program.verifier c.i.data true true c.world.saved
    (writeBracket c.i.entry.heap 2 0 0 (source (nativeBytes c.world.saved))) ac1
 · exact Rc2_Events.derive _ (hashv c) n1 n2 ext copy NNE_AbortIndicator.allocator
    CPH_Program.verifier c.sha256 c.sha256 (DGP_HostDigest.p1 c.sha256)
    (DGP_HostDigest.syscall c.sha256) c.world.saved
 · exact CPH_Protection.derive c.world.p c.world.t c.world.u c.i.entry c.j.entry c.world.saved
    c.world.actions selected (Rc5_Install.key c.fixed.indexError selected c.fixed.reservation)
    n1 n2 (hashv c) ext copy std NNE_AbortIndicator.allocator CPH_Program.verifier game.1
    c.i.data true true (writeBracket c.i.entry.heap 2 0 0 (source (nativeBytes c.world.saved))) ac1
 · exact CPH_Trace.derive game.1
 · exact CPH_Recorder.physical c.world.p c.world.t c.world.u c.i.entry c.j.entry c.world.saved
    c.world.actions cfg n1 n2 (hashv c) ext copy NNE_AbortIndicator.allocator
    CPH_Program.verifier game.1 c.sha256 c.sha256 (DGP_HostDigest.p1 c.sha256)
    (DGP_HostDigest.syscall c.sha256)
#print axioms rest
end AspisR1.NNH_Run5bRest
end
