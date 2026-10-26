import F3U_BytePreparation
import F3V_SdkPreparation
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3V_BytePreparation
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
      AspisR1CurrentCaller.verifier.candidate.prepare
        (RowShape_InstalledSlots.verifierOps
          (Op5T_Concrete.current {(GExp_FirstPair.base c.currentBase c.reserved c.query c.geometry) with op16:=Tx1Q_Install.writer})
          c.boundaries c.std)
        (F3V_OracleDictionary.current H (currentDigest c))
        (AspisS6CurrentVerifierCarrier.toPublic semantic) proof () none
        (Array.repeat 29#usize zero)=ok (.Ok p,scratch) := by
  obtain ⟨pub,proof,semantic,zero,p,scratch,hpub,hproof,decoded,prepare⟩ :=
    F3U_BytePreparation.accepted c hashv s H accepted
  rw [F3V_SdkPreparation.same, SdkD_PrepareSource.source] at prepare
  exact ⟨pub,proof,semantic,zero,p,scratch,hpub,hproof,decoded,prepare⟩

#print axioms accepted
end AspisR1.F3V_BytePreparation
end
