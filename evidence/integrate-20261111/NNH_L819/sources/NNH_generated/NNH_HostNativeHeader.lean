import NNH_HostNativeCuts
import NNH_HostOracle
import NNH_064EnvHeader
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_HostNativeHeader
open Aeneas Aeneas.Std Result NNH_HostCtx NNH_Libraries
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open MultiproofConeCanonical

theorem reader {W Tx : Type} (c : Ctx W Tx) (p : NNH_HostNativeCuts.Packet c) :
 NLW_ReaderHeader.decode (bytesOf p.s.checkpoint.val) =
  some (c.sha256 (bytesOf p.s.proof.val),c.sha256 (bytesOf p.s.pub.val)) := by
 have header := NNH_064EnvHeader.native (envOf c) p.s.pub p.s.proof p.s.checkpoint
  NNH_064Install.frame p.domain p.records p.events p.native
 rw [NNH_HostOracle.singleton_oracle,NNH_HostOracle.singleton_oracle] at header
 exact header

theorem selected_clock {W Tx : Type} (c : Ctx W Tx) (p : NNH_HostNativeCuts.Packet c) :
 P2P_NativeSelection.pair (sdk c) CPH_Program.verifier c.i.entry c.j.entry
  c.j.data (NNH_HostWeak241.clock (envOf c)) = Hist_PairExperiment.select ⟨p.f,p.s⟩ :=
 NNC_SourceCuts.on_cuts (sdk c) CPH_Program.verifier c.i.entry c.j.entry c.j.data
  (NNH_HostWeak241.clock (envOf c)) c.world.saved p.f p.s p.cuts p.origin

/-- A precise intermediate implication only: the SAME weak records suffice
for Root0 once the actual selected pair is bound. This is not the host field;
its missing selected-pair equality is deliberately visible. -/
theorem root_of_binding {W Tx : Type} (c : Ctx W Tx) (p : NNH_HostNativeCuts.Packet c)
 (binding : R9PoolRuntimeBinding.P2Prime c.sha256
  ⟨bytesOf p.f.proof.val,bytesOf p.f.pub.val⟩ ⟨bytesOf p.s.proof.val,bytesOf p.s.pub.val⟩) :
 NLP_InputDomain.Root0 p.s.checkpoint p.s.proof :=
 NNC_BindingRoot.root0_of_binding c.sha256 c.world.saved p.f p.s p.writerRoot
  p.persisted p.writerHeader (reader c p) binding
#print axioms reader
#print axioms selected_clock
#print axioms root_of_binding
end AspisR1.NNH_HostNativeHeader
end
