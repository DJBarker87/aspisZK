import NNR_Retime
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNR_Producers
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open NNH_HostCtx NNH_LiteralHost NNH_Libraries S2W_NativeConsolidation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep MultiproofConeCanonical
variable {W Tx : Type} (L0 : Library W (Nat → Record))
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy)

theorem accepted (c : Ctx W Tx) :
 (S_host L0 copy std).Accepted1 (NNR_Retime.atSlot c) (model1 (NNR_Retime.atSlot c)) ↔
 (S_host L0 copy std).Accepted1 c (model1 c) := by
 change S2W_D189Wrappers.first (model1 (NNR_Retime.atSlot c)) copy NNE_AbortIndicator.allocator
  c.i.entry CPH_Program.verifier c.i.data true = _ ↔ _
 rw [NNR_Retime.first]
 rfl

theorem game (c : Ctx W Tx) :
 (S_host L0 copy std).Game (NNR_Retime.atSlot c) (model1 (NNR_Retime.atSlot c)) (model2 (NNR_Retime.atSlot c)) ↔
 (S_host L0 copy std).Game c (model1 c) (model2 c) := by
 change (CPH_Game.DeployedPairExecution c.world.p c.world.t c.world.u c.i.entry c.j.entry
  c.world.saved c.world.actions (model1 (NNR_Retime.atSlot c)) (model2 (NNR_Retime.atSlot c))
  copy NNE_AbortIndicator.allocator CPH_Program.verifier ∧ retained L0 c) ↔ _
 rw [NNR_Retime.first,NNR_Retime.second]
 rfl

theorem produce (c : Ctx W Tx) (post : RSL.SdkState) (events : List RSL.Event)
 (ref : RSL.TX2_213.Ref L D (RSL.TAS.lib V0 (fun _ _ => True) NNH_064WeakField.w)
  (RSL.TX1_344.asStage1 VL P C)
  (NNE_EntryArgs.args c.j.entry 7 CPH_Program.verifier c.j.data)
  (NNE_Entry.state c.j.entry 0) (NFB_NMFBHost.env2 c) ⟨.ret (.ok (),post),events⟩)
 (acc : (S_host L0 copy std).Accepted1 c (model1 c))
 (run : (S_host L0 copy std).Game c (model1 c) (model2 c)) :
 Nonempty (NNH_HostNativeCuts.Packet (NNR_Retime.atSlot c)) :=
 NNH_HostNativeCuts.produce L0 copy std (NNR_Retime.atSlot c) post events ref
  ((accepted L0 copy std c).mpr acc) ((game L0 copy std c).mpr run)

theorem origin (c : Ctx W Tx) (p : NNH_HostNativeCuts.Packet (NNR_Retime.atSlot c)) :
 P2P_Origin.Fact (sdk c) CPH_Program.verifier (c.j.entry.second secondSizes) c.j.data c.j.slot p.s := by
 have h := p.origin
 rw [NNR_Retime.sdk_same,NNR_Retime.env,NNR_Clock.M1a] at h
 exact h
#print axioms accepted
#print axioms game
#print axioms produce
#print axioms origin
end AspisR1.NNR_Producers
end
