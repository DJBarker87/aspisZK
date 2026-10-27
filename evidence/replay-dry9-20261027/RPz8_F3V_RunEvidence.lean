import RPz8_F3V_AllWorldNative
import RPz8_F3V_SecondRun
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3V_RunEvidence
open Aeneas Aeneas.Std Result MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open DrvC_Installation F3T_ByteCarrier

abbrev D1 {F C : Type} (c : Configuration F C) (H : Bytes → State) :=
  F3V_OracleDictionary.current H (currentDigest c)
abbrev D2 {F C : Type} (c : Configuration F C) (H : Bytes → State) :=
  F3V_StageDictionary.ideal H (digest c)

/-- Output witnesses of one accepted byte/H execution, not a premise contract. -/
structure Evidence {F C : Type} (c : Configuration F C) (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (s : Submission) (H : Bytes → State) where
  pub : Slice U8
  proof : Slice U8
  semantic : Port1_Driver.Semantic
  saved : alloc.vec.Vec U8
  pubBytes : bytesOf pub.val=s.publicBytes
  proofBytes : bytesOf proof.val=s.stored
  decoded : Port1_Driver.decodeSemantic (sdk c) pub=ok (some semantic)
  header : OraclePortHeader.accepts (bytesOf proof.val)=true
  canonical : OraclePortCompactDraft.scan (bytesOf proof.val)
  run : Tx1Q_Execution.Run
    (Tx1Q_Execution.actual (Op5T_Concrete.current c.currentBase) c.reserved c.query c.geometry c.boundaries c.std)
    c.reserved c.query c.geometry (D1 c H) ()
    (AspisS6CurrentVerifierCarrier.toPublic semantic) pub proof 10#usize saved
  zero : AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact.ZERO
    (Tx1Q_Execution.actual (Op5T_Concrete.current c.currentBase) c.reserved c.query c.geometry c.boundaries c.std)=ok run.zero
  rootView : Slice U8
  rootRange : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    proof {start:=7751#usize,«end»:=7783#usize}=ok rootView
  rootCopy : core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 rootView=ok (.Ok run.root)
  second : VTop_Stages.verifier.candidate.tx2_authenticated
    (GExp_SecondCode.installed (stage c) c.reserved) (D2 c H) pub proof saved.deref () none=ok (.Ok ())
  prepared : F3V_PreparedFacts.Facts (Op5T_Concrete.current c.currentBase) c.reserved c.query c.geometry
    B c.std (D1 c H) semantic pub proof run.p run.zero H

end AspisR1.F3V_RunEvidence
end
