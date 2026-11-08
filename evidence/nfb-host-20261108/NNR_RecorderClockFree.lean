import NNR_Producers
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNR_RecorderClockFree
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open NNH_HostCtx

theorem event {W Tx : Type}
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (c : Ctx W Tx) :
 NNH_HostExec.ERec copy (NNR_Retime.atSlot c).fixed c.sha256 =
 NNH_HostExec.ERec copy c.fixed c.sha256 := by
 unfold NNH_HostExec.ERec
 dsimp only [NNR_Retime.atSlot]
 rw [NNR_ClockFree.M1b c.sha256 c.fixed.pda
  (NND_Carrier.reply NND_Carrier.slot c.j.slot) c.fixed.clock c.fixed.reservation]
#print axioms event
end AspisR1.NNR_RecorderClockFree
end
