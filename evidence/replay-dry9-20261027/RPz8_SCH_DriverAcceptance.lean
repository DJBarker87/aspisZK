import RPz8_SCH_IdealFirst
import RPz8_SCH_IdealSecond
import RPz7_F3T_Installed
import RPz7_DrvC_Bytes
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCH_DriverAcceptance
open Aeneas Aeneas.Std Result MultiproofConeCanonical S2W_NativeConsolidation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- Direct ideal-account-source to installed standalone driver acceptance.
The three byte associations remain explicit local obligations; this theorem
neither assumes native success nor claims to discharge those associations. -/
theorem accepted {F C : Type} (c : DrvC_Installation.Configuration F C)
    (err : C) (reservation : NP6_StdModel.Reservation)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (H : Bytes → State)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts) (saved : alloc.vec.Vec U8)
    (f : FirstCut) (s : SecondCut) :
    let r := Rc5_Install.configuration err c reservation
    SourceCuts (SCH_IdealSdk.dictionary r hashv H) accounts1 accounts2 saved f s →
    Port1_Driver.decodeSemantic (DrvC_Installation.sdk r) f.pub = ok (some f.semantic) →
    bytesOf s.proof.val = bytesOf f.proof.val →
    bytesOf s.pub.val = bytesOf f.pub.val →
    bytesOf s.checkpoint.val = bytesOf saved.val →
    (eval H (F3T_Installed.source r hashv
      (F3T_ByteCarrier.input r ⟨bytesOf f.pub.val,bytesOf f.proof.val⟩))).2 = true := by
  dsimp only
  intro cuts decoded proof pub checkpoint
  have one := SCH_IdealFirst.accepted c err reservation hashv H f.semantic f.pub f.proof f.split saved cuts.first
  have two := SCH_IdealSecond.accepted c err reservation hashv H s.pub s.proof s.checkpoint cuts.second
  rw [DrvC_Bytes.slice_injective s.proof f.proof proof,
    DrvC_Bytes.slice_injective s.pub f.pub pub,
    DrvC_Bytes.slice_injective s.checkpoint saved.deref checkpoint] at two
  simp only [F3T_Installed.source,F3T_ByteCarrier.input,DrvC_Bytes.asSlice,decoded,
    DrvC_PairProgram.source,eval_bind,one,two,Port1_Driver.verdict,eval]

#print axioms accepted
end AspisR1.SCH_DriverAcceptance
end
