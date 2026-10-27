import FGl_Join
import SCG_SourceAcceptance
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCG_Composition
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open DrvC_Installation F3T_ByteCarrier

/-- Pointwise composition on the exact installed native cuts. The collision
alternative names the SOURCE recorder explicitly; it is not the physical
account event, and no premise removal is claimed from this intermediate. -/
theorem native_join_or_source_collision {F C : Type} (base : Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : LiteralByteProtocol.Decoder) (w : CanonicalCutEnrichedTranscript.Words)
    (prior : Program Bytes State Unit) (Q : Nat)
    (queries : ∀ H : Bytes → State,(eval H prior).1.length≤Q)
    (select : F3X_Projection.Output → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs) :
    let c := F3V_Install.configuration base
    ∀ (prepareOwner : WAdm_Domain.SessionAPrepare
      (Tx1Q_Execution.actual (Op5T_Concrete.current c.currentBase) c.reserved c.query c.geometry c.boundaries c.std))
    (primitiveOwner : Port5Q1_QueryPorts.SessionAPrimitives c.query)
    (canonicalOwner : Port5Q1_GeometryCanonical.SessionAPrimitives c.geometry)
    (domainOwner : Port5Q1_Domain.SessionADomain c.geometry)
    (multiply : c.geometry.op9=AspisR1Qm31ArithmeticProbe.field.M31.mul)
    (one : c.geometry.op7=ok (1#u32)) (inverse : c.geometry.op11=Port4C_InverseExecution.inverse_owned)
    (finishOwners : FGl_PreparedAt.Owners c base.boundaries),
    ∀ (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (extraction : S2W_DigestExtraction.AeneasExtraction (sdk c) native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts) (saved : alloc.vec.Vec U8)
    (f : S2W_NativeConsolidation.FirstCut) (next : S2W_NativeConsolidation.SecondCut)
    (cuts : S2W_NativeConsolidation.SourceCuts (sdk c) accounts1 accounts2 saved f next)
    (decoded : Port1_Driver.decodeSemantic (sdk c) f.pub = ok (some f.semantic))
    (proof : MultiproofConeCanonical.bytesOf next.proof.val = MultiproofConeCanonical.bytesOf f.proof.val)
    (pub : MultiproofConeCanonical.bytesOf next.pub.val = MultiproofConeCanonical.bytesOf f.pub.val)
    (checkpoint : MultiproofConeCanonical.bytesOf next.checkpoint.val = MultiproofConeCanonical.bytesOf saved.val),
    let s : Submission := ⟨MultiproofConeCanonical.bytesOf f.pub.val,MultiproofConeCanonical.bytesOf f.proof.val⟩;

      eval H (F3T_Installed.source c hashv (input c s))=
        eval H (F3_Model.verifier D (input c s)) ∨
      BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q+2965)
        (eval H (Hiq_RecordedJoint.program (F3X_AccountPrior.program c hashv prior s)
          F3X_Projection.project select)) := by
  dsimp only
  intro prepareOwner primitiveOwner canonicalOwner domainOwner multiply one inverse finishOwners
    native1 native2 extraction sha256 H p1 syscall accounts1 accounts2 saved f next cuts
    decoded proof pub checkpoint
  exact FGl_Join.accepted_raw_join_or_collision base hashv D w prior Q queries select
    prepareOwner primitiveOwner canonicalOwner domainOwner multiply one inverse finishOwners _ H
    (SCG_SourceAcceptance.installed _ native1 native2 hashv extraction sha256 H p1 syscall
      accounts1 accounts2 saved f next cuts decoded proof pub checkpoint)

#print axioms native_join_or_source_collision
end AspisR1.SCG_Composition
end
