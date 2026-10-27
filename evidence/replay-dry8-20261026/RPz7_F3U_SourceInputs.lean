import RPz7_F3T_ByteCarrier
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3U_SourceInputs
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open F3T_ByteCarrier

theorem accepted {F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (s : Submission) (H : Bytes → State)
    (accepted : (eval H (F3T_Installed.source c hashv (input c s))).2=true) :
    ∃ (pub proof : Slice U8) (semantic : Port1_Driver.Semantic),
      Port1_Driver.asSlice s.publicBytes=some pub ∧ Port1_Driver.asSlice s.stored=some proof ∧
      Port1_Driver.decodeSemantic (DrvC_Installation.sdk c) pub=ok (some semantic) ∧
      F3T_Installed.source c hashv (input c s)=DrvC_PairProgram.source c hashv semantic pub proof ∧
      (eval H (DrvC_PairProgram.source c hashv semantic pub proof)).2=true := by
  cases hp : Port1_Driver.asSlice s.publicBytes with
  | none => simp only [F3T_Installed.source,input,hp,eval] at accepted;cases accepted
  | some pub =>
    cases hs : Port1_Driver.asSlice s.stored with
    | none => simp only [F3T_Installed.source,input,hp,hs,eval] at accepted;cases accepted
    | some proof =>
      cases hd : Port1_Driver.decodeSemantic (DrvC_Installation.sdk c) pub with
      | fail e => simp only [F3T_Installed.source,input,hp,hs,hd,eval] at accepted;cases accepted
      | div => simp only [F3T_Installed.source,input,hp,hs,hd,eval] at accepted;cases accepted
      | ok semantic => cases semantic with
        | none => simp only [F3T_Installed.source,input,hp,hs,hd,eval] at accepted;cases accepted
        | some semantic =>
          have source : F3T_Installed.source c hashv (input c s)=DrvC_PairProgram.source c hashv semantic pub proof := by
            simp only [F3T_Installed.source,input,hp,hs,hd]
          exact ⟨pub,proof,semantic,rfl,rfl,hd,source,source ▸ accepted⟩

#print axioms accepted
end AspisR1.F3U_SourceInputs
end
