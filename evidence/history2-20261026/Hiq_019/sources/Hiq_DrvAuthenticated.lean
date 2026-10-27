import Hiq_DrvWriterHeader
import Hiq_DrvReaderHeader
import Hiq_CausalVersion
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hiq_DrvAuthenticated
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2W_D189Entry S2W_D189Wrappers S2W_NativeConsolidation DrvC_Installation MultiproofConeCanonical
open S2W_AuthenticatedInputs
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

theorem inputs {F C : Type} (c : Configuration F C)
    (keyLaw : (sdk c).op36 = Hist_Authority.keyEq)
    (owner : WAdm_Domain.SessionAPrepare
      (Tx1Q_Execution.actual (Op5T_Concrete.current c.currentBase) c.reserved c.query c.geometry c.boundaries c.std))
    (ports : Port5Q1_QueryPorts.SessionAPrimitives c.query)
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
    bytesOf s.proof.val = bytesOf f.proof.val ∧ bytesOf s.pub.val = bytesOf f.pub.val ∧
      bytesOf s.checkpoint.val = bytesOf saved.val ∧ saved.val.length = 1768 := by
  have shape := Hiq_DrvShape.on_cuts c _ _ saved f s cuts owner ports
  let version := Hiq_CausalVersion.version (sdk c) keyLaw id initial final l1 l2 data saved accepted
    events trace sameKey shape.1 f s cuts
  have persisted := S2X.checkpoint_persistence _ _ version
  have wrote := Hiq_DrvWriterHeader.header c _ _ saved f s cuts owner ports H oracle
  have read := Hiq_DrvReaderHeader.header c _ _ saved f s cuts H oracle
  rw [persisted,wrote] at read
  have paired := Option.some.inj read
  have matched : R9PoolRuntimeBinding.digestMatches H
      ⟨bytesOf f.proof.val,bytesOf f.pub.val⟩ ⟨bytesOf s.proof.val,bytesOf s.pub.val⟩ :=
    ⟨(congrArg Prod.fst paired).symm,(congrArg Prod.snd paired).symm⟩
  obtain ⟨proof,pub⟩ := binding.binding matched
  exact ⟨proof,pub,persisted,shape.2⟩

#print axioms inputs
end AspisR1.Hiq_DrvAuthenticated
end
