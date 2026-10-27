import Hiq_LightAuthenticated
import Hiq_CarrierIdentity
import Hiq_DrvReaderHeader
import Hiq_CausalVersion
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hiq_AuthenticatedPrograms
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2W_D189Entry S2W_D189Wrappers S2W_NativeConsolidation DrvC_Installation MultiproofConeCanonical
open S2W_AuthenticatedInputs
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

theorem inputs {F C : Type} (c : Configuration F C)
    (keyLaw : (sdk c).op36 = Hist_Authority.keyEq)
    (id : S2W_ExtractionBoundary.Program) (initial final : Store) (l1 l2 : Layout)
    (data : Slice U8) (saved : alloc.vec.Vec U8)
    (accepted : AdapterRw.r1_pool_adapter.owned.stage1_owned (sdk c) id (load initial l1).first data = ok (.Ok saved))
    (events : List S2X.AccountEvent)
    (trace : Trace (sdk c) id (commit initial (l1.handles 2).1 saved) events final)
    (sameKey : (l2.handles 6).1 = (l1.handles 2).1)
    (f : FirstCut) (s : SecondCut)
    (cuts : SourceCuts (sdk c) (load initial l1).first ((load final l2).second secondSizes) saved f s)
    (H : Bytes → State) (oracle : CheckpointBytes5Inputs.Oracle (S2Z.Oracle.leadDigest (sdk c)) () H)
    (binding : P2Prime H f.proof f.pub s.proof s.pub) :
    bytesOf s.checkpoint.val = bytesOf saved.val ∧ saved.val.length = 1768 ∧
      DrvC_Implementation.driver c (Hiq_CanonicalCarrier.input s.pub s.proof) =
        DrvC_Implementation.driver c (Hiq_CanonicalCarrier.input f.pub f.proof) := by
  obtain ⟨proof,pub,checkpoint,size⟩ := Hiq_LightAuthenticated.inputs c keyLaw id initial final l1 l2 data saved
    accepted events trace sameKey f s cuts H oracle binding
  refine ⟨checkpoint,size,?_⟩
  rw [Hiq_CarrierIdentity.input_same f.pub f.proof s.pub s.proof proof pub]

#print axioms inputs
end AspisR1.Hiq_AuthenticatedPrograms
end
