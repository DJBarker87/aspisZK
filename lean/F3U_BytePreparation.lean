import F3U_AllWorldMachine
import F3U_AllWorldPreparedValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3U_BytePreparation
open Aeneas Aeneas.Std Result MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open DrvC_Installation F3T_ByteCarrier

theorem accepted {F C : Type} (c : Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (s : Submission) (H : Bytes → State)
    (accepted : (eval H (F3T_Installed.source c hashv (input c s))).2=true) :
    ∃ (pub proof : Slice U8) (semantic : Port1_Driver.Semantic)
      (zero : AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact)
      (p : AspisR1CurrentCaller.verifier.Prepared)
      (scratch : Array AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact 29#usize),
      bytesOf pub.val=s.publicBytes ∧ bytesOf proof.val=s.stored ∧
      Port1_Driver.decodeSemantic (sdk c) pub=ok (some semantic) ∧
      AspisR1PublicPreparation.PreparedHashCode.erase (F3U_Rehash.code H
        (SdkD_PrepareSource.code
          (Op5T_Concrete.current {(GExp_FirstPair.base c.currentBase c.reserved c.query c.geometry) with op16:=Tx1Q_Install.writer})
          c.boundaries c.std (currentDigest c) (AspisS6CurrentVerifierCarrier.toPublic semantic) proof ()
          (Array.repeat 29#usize zero)))=ok (.Ok p,scratch) := by
  obtain ⟨pub,proof,semantic,hpub,hproof,decoded,source,ha⟩ := F3U_SourceInputs.accepted c hashv s H accepted
  obtain ⟨zero,p,scratch,prepare⟩ := F3U_AllWorldPreparedValue.accepted c hashv semantic pub proof H ha
  exact ⟨pub,proof,semantic,zero,p,scratch,F3U_AsSliceBytes.inverse _ _ hpub,
    F3U_AsSliceBytes.inverse _ _ hproof,decoded,prepare⟩

#print axioms accepted
end AspisR1.F3U_BytePreparation
end
