import NNH_Run5bExec
import NNR_Lift
import NNR_Oracle
import NNR_RootImage
import NNR_RecorderClockFree
import NNH_NMFPrime
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_Run5bPacket
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open NNH_Run5bCtx NNH_Run5bHost NNH_Libraries S2W_NativeConsolidation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open MultiproofConeCanonical
variable {W Tx : Type}

abbrev Cut (c : Ctx W Tx) := NNH_HostNativeCuts.Packet (NNR_Retime.atSlot c)

theorem cuts (c : Ctx W Tx) (p : Cut c) :
 NNC_SourceCuts.Cuts (sdk c) c.i.entry.first (c.j.entry.second secondSizes) c.world.saved p.f p.s := by
 have h := p.cuts
 rw [NNR_Retime.sdk_same] at h
 exact h

def source
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (c : Ctx W Tx) := NNH_RecordedCharge.source copy (base c) c.fixed.indexError
 c.fixed.reservation (hashv c) c.fixed.a (c.fixed.Q0+c.fixed.Q1)

def select (c : Ctx W Tx) := ARQ_Observer.select (configuration c) CPH_Program.verifier

def packet
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (c : Ctx W Tx) (p : Cut c)
 (sel : select c (eval c.sha256 (source copy c)).2 =
 P2P_NativeSelection.pair (sdk c) CPH_Program.verifier c.i.entry c.j.entry c.j.data c.j.slot) : NNH_NMFPrime.Packet (GExq_AccountExperiment.Outcome Bool) Unit Unit := by
 have native := NNR_Lift.M2 c.sha256 c.fixed.pda
  (NND_Carrier.reply NND_Carrier.slot c.j.slot) c.fixed.reservation
  p.s.pub p.s.proof p.s.checkpoint p.records p.events p.domain p.native
 let records := Classical.choose native
 let ev := Classical.choose (Classical.choose_spec native)
 have step := Classical.choose_spec (Classical.choose_spec native)
 exact (⟨source copy c,ARQ_Observer.project,select c,c.fixed.Q0+c.fixed.Q1,
  fun H => (VerifierCallBudget.firstReads_le_length _ _).trans (ARX_LocalCharge.budget _ _ H),
  c.sha256,sdk c,CPH_Program.verifier,c.i.entry,c.j.entry,c.j.data,c.j.slot,sel,
  c.world.saved,p.f,p.s,cuts c p,NNR_Producers.origin c p,
  p.writerRoot,p.persisted,p.writerHeader,LIBB_PartitionEnv.digest (envOf c),(),
  NNH_064Install.frame,p.domain,
  NNR_Oracle.M2e c.sha256 c.fixed.pda _ c.fixed.reservation,records,ev,step⟩ :
  NNH_NMFPrime.Packet _ Unit Unit)

#print axioms cuts
#print axioms packet
end AspisR1.NNH_Run5bPacket
end
