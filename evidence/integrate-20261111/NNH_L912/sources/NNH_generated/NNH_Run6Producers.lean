import NNR_Producers
import NNH_Run6Cuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_Run6Producers
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open NNH_HostCtx NNH_LiteralHost NNH_Libraries S2W_NativeConsolidation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep MultiproofConeCanonical
variable {W Tx : Type} (L0 : Library W (Nat → Record))
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy)

theorem produce (c : Ctx W Tx) (post : RSL.SdkState) (events : List RSL.Event)
 (ref : RSL.TX2_213.Ref L D (RSL.TAS.lib V0 (fun _ _ => True) V0.tx2auth)
  (RSL.TX1_344.asStage1 VL P C)
  (NNE_EntryArgs.args c.j.entry 7 CPH_Program.verifier c.j.data)
  (NNE_Entry.state c.j.entry 0) (NFB_NMFBHost.env2 c) ⟨.ret (.ok (),post),events⟩)
 (acc : (S_host L0 copy std).Accepted1 c (model1 c))
 (run : (S_host L0 copy std).Game c (model1 c) (model2 c)) :
 Nonempty (NNH_HostNativeCuts.Packet (NNR_Retime.atSlot c)) :=
 NNH_Run6Cuts.produce L0 copy std (NNR_Retime.atSlot c) post events ref
  ((NNR_Producers.accepted L0 copy std c).mpr acc) ((NNR_Producers.game L0 copy std c).mpr run)

#print axioms produce
end AspisR1.NNH_Run6Producers
end
