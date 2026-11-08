import NNH_HostFirstWriter
import NNC_NativePersistence
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_HostPersistence
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open MultiproofConeCanonical NNH_HostCtx NNH_LiteralHost S2W_NativeConsolidation
variable {W Tx : Type} (L : Library W (Nat → Record))
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy)

theorem key (c : Ctx W Tx) : (sdk c).op36 = Hist_Authority.keyEq :=
 Rc5_Install.key c.fixed.indexError (FIp_Install.select c.fixed.reservation (base c)) c.fixed.reservation

/-- Root0-free persistence of the SAME selected checkpoint. Cuts/length are
intermediate native-record facts still to be produced by the packet builder;
this is not the final NMF_B field. No second model acceptance is used. -/
theorem persisted (c : Ctx W Tx)
 (accepted : (S_host L copy std).Accepted1 c (model1 c))
 (game : (S_host L copy std).Game c (model1 c) (model2 c))
 (f : FirstCut) (s : SecondCut)
 (cuts : NNC_SourceCuts.Cuts (sdk c) c.i.entry.first
  (c.j.entry.second secondSizes) c.world.saved f s)
 (length : s.checkpoint.val.length = 1768) :
 bytesOf s.checkpoint.val = bytesOf c.world.saved.val := by
 exact NNC_NativePersistence.persisted c.world.p c.world.t c.world.u (configuration c) (key c)
  c.i.entry c.j.entry c.world.saved c.world.actions (model1 c) (model2 c) (hashv c)
  (NNH_HostCtx.extraction c) copy std NNE_AbortIndicator.allocator CPH_Program.verifier
  (Hist_Nonvacuity.key 0#u8) CPH_Program.not_system game.1 game.2.2.2
  c.i.data true true (NNH_HostExec.post c.i c.world.saved) accepted f s cuts length
#print axioms key
#print axioms persisted
end AspisR1.NNH_HostPersistence
end
