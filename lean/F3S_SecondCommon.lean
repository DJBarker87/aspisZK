import F3S_Silent
import F3S_Residual
import F3R_Try
import GExq_SecondCode
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3S_SecondCommon
open Aeneas Aeneas.Std Result CheckpointBytes5Effect VTop_Stages
local instance : MonadLift Result Code where monadLift := CheckpointBytes5Effect.liftResult
attribute [local irreducible] GExq_RetainedReader.code GExq_BatchSource.stage
 theorem split {Hash : Type} (base : Ops) (reserved : Bool)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (D : aspis_core.digest.Digest32 Hash)
    (pub proof checkpoint : Slice U8) (hash : Hash)
    (success : erase (SdkC_Source.dictionary hashv) ()
      (GExq_SecondCode.common base reserved hashv D pub proof checkpoint hash)=ok (.Ok ())) :
    ∃ (p : verifier.Prepared) (acc : verifier.Accumulator) (root : Array U8 32#usize),
      erase (SdkC_Source.dictionary hashv) () (GExq_RetainedReader.code reserved checkpoint proof pub .S2)=ok (.Ok (p,acc)) ∧
      erase (SdkC_Source.dictionary hashv) () (GExq_BatchSource.stage D hash proof p root)=ok (.Ok ()) ∧
      SdkC_Source.readLog (SdkC_Source.run hashv
        (GExq_SecondCode.common base reserved hashv D pub proof checkpoint hash) []).2=
        SdkC_Source.readLog (SdkC_Source.run hashv (GExq_RetainedReader.code reserved checkpoint proof pub .S2) []).2 ++
        SdkC_Source.readLog (SdkC_Source.run hashv (GExq_BatchSource.stage D hash proof p root) []).2 := by
  generalize eqLog : SdkC_Source.readLog (SdkC_Source.run hashv
    (GExq_SecondCode.common base reserved hashv D pub proof checkpoint hash) []).2=original
  have logs := eqLog.symm
  unfold GExq_SecondCode.common at success logs
  obtain ⟨reader,h0,s0,l0⟩ := GExq_CodeTrace.success_bind hashv _ _ _ success
  erw [l0] at logs
  obtain ⟨cfReader,h1,s1,l1⟩ := F3R_SdkPure.right hashv _ _ _ s0
  erw [l1] at logs
  cases cfReader with
  | Break residual =>
    cases residual with
    | Ok u => cases u
    | Err e => exact False.elim (F3S_Residual.impossible hashv e () s1)
  | Continue pair =>
    rcases pair with ⟨p,acc⟩
    obtain ⟨index,h2,s2,l2⟩ := F3R_SdkPure.right hashv _ _ _ s1
    erw [l2] at logs
    by_cases bad : (acc.next != index)=true
    · simp only [bad,if_true,erase] at s2; cases s2
    ·
      simp only [bad,if_false] at s2 logs
      obtain ⟨powers,h3,s3,l3⟩ := F3R_SdkPure.right hashv _ _ _ s2
      erw [l3] at logs
      obtain ⟨markRead,h4,s4,l4⟩ := F3R_SdkPure.right hashv _ _ _ s3
      erw [l4] at logs
      obtain ⟨offInactive,h5,s5,l5⟩ := F3R_SdkPure.right hashv _ _ _ s4
      erw [l5] at logs
      obtain ⟨offRound0,h6,s6,l6⟩ := F3R_SdkPure.right hashv _ _ _ s5
      erw [l6] at logs
      obtain ⟨inactiveView,h7,s7,l7⟩ := F3R_SdkPure.right hashv _ _ _ s6
      erw [l7] at logs
      obtain ⟨inactiveOption,h8,s8,l8⟩ := F3R_SdkPure.right hashv _ _ _ s7
      erw [l8] at logs
      obtain ⟨inactiveResult,h9,s9,l9⟩ := F3R_SdkPure.right hashv _ _ _ s8
      erw [l9] at logs
      obtain ⟨cfInactive,h10,s10,l10⟩ := F3R_SdkPure.right hashv _ _ _ s9
      erw [l10] at logs
      cases cfInactive with
      | Break residual =>
        cases residual with
        | Ok u => cases u
        | Err e => exact False.elim (F3S_Residual.impossible hashv e () s10)
      | Continue inactive =>
        obtain ⟨offRoot,h11,s11,l11⟩ := F3R_SdkPure.right hashv _ _ _ s10
        erw [l11] at logs
        obtain ⟨offRound1,h12,s12,l12⟩ := F3R_SdkPure.right hashv _ _ _ s11
        erw [l12] at logs
        obtain ⟨rootView,h13,s13,l13⟩ := F3R_SdkPure.right hashv _ _ _ s12
        erw [l13] at logs
        obtain ⟨rootResult,h14,s14,l14⟩ := F3R_SdkPure.right hashv _ _ _ s13
        erw [l14] at logs
        obtain ⟨root,h15,s15,l15⟩ := F3R_SdkPure.right hashv _ _ _ s14
        erw [l15] at logs
        obtain ⟨batchResult,h16,s16,l16⟩ := GExq_CodeTrace.success_bind hashv _ _ _ s15
        erw [l16] at logs
        obtain ⟨cfBatch,h17,s17,l17⟩ := F3R_SdkPure.right hashv _ _ _ s16
        erw [l17] at logs
        cases cfBatch with
        | Break residual =>
          cases residual with
          | Ok u => cases u
          | Err e => exact False.elim (F3S_Residual.impossible hashv e () s17)
        | Continue batchUnit =>
          obtain ⟨markBatch,h18,s18,l18⟩ := F3R_SdkPure.right hashv _ _ _ s17
          erw [l18] at logs
          obtain ⟨queryResult,h19,s19,l19⟩ := F3R_SdkPure.right hashv _ _ _ s18
          erw [l19] at logs
          obtain ⟨cfQuery,h20,s20,l20⟩ := F3R_SdkPure.right hashv _ _ _ s19
          erw [l20] at logs
          cases cfQuery with
          | Break residual =>
            cases residual with
            | Ok u => cases u
            | Err e => exact False.elim (F3S_Residual.impossible hashv e () s20)
          | Continue queryState =>
            obtain ⟨weightResult,h21,s21,l21⟩ := F3R_SdkPure.right hashv _ _ _ s20
            erw [l21] at logs
            obtain ⟨cfWeight,h22,s22,l22⟩ := F3R_SdkPure.right hashv _ _ _ s21
            erw [l22] at logs
            cases cfWeight with
            | Break residual =>
              cases residual with
              | Ok u => cases u
              | Err e => exact False.elim (F3S_Residual.impossible hashv e () s22)
            | Continue weightState =>
              obtain ⟨advanceResult,h23,s23,l23⟩ := F3R_SdkPure.right hashv _ _ _ s22
              erw [l23] at logs
              obtain ⟨cfAdvance,h24,s24,l24⟩ := F3R_SdkPure.right hashv _ _ _ s23
              erw [l24] at logs
              cases cfAdvance with
              | Break residual =>
                cases residual with
                | Ok u => cases u
                | Err e => exact False.elim (F3S_Residual.impossible hashv e () s24)
              | Continue advance =>
                rcases advance with ⟨a,pending⟩
                obtain ⟨borrow,h25,s25,l25⟩ := F3R_SdkPure.right hashv _ _ _ s24
                erw [l25] at logs
                rcases borrow with ⟨weights,back⟩
                obtain ⟨flushed,h26,s26,l26⟩ := F3R_SdkPure.right hashv _ _ _ s25
                erw [l26] at logs
                obtain ⟨empty1,h27,s27,l27⟩ := F3R_SdkPure.right hashv _ _ _ s26
                erw [l27] at logs
                obtain ⟨empty2,h28,s28,l28⟩ := F3R_SdkPure.right hashv _ _ _ s27
                erw [l28] at logs
                obtain ⟨round0,h29,s29,l29⟩ := F3R_SdkPure.right hashv _ _ _ s28
                erw [l29] at logs
                obtain ⟨offFinal,h30,s30,l30⟩ := F3R_SdkPure.right hashv _ _ _ s29
                erw [l30] at logs
                obtain ⟨round1,h31,s31,l31⟩ := F3R_SdkPure.right hashv _ _ _ s30
                erw [l31] at logs
                obtain ⟨offQuery,h32,s32,l32⟩ := F3R_SdkPure.right hashv _ _ _ s31
                erw [l32] at logs
                obtain ⟨finalMessage,h33,s33,l33⟩ := F3R_SdkPure.right hashv _ _ _ s32
                erw [l33] at logs
                obtain ⟨empty3,h34,s34,l34⟩ := F3R_SdkPure.right hashv _ _ _ s33
                erw [l34] at logs
                have readerEq := F3R_Try.continued reader (p,acc) h1
                have batchEq := F3R_Try.continued batchResult batchUnit h17
                refine ⟨p,acc,root,?_,?_,?_⟩
                · simpa only [readerEq] using h0
                · simpa only [batchEq] using h16
                · simpa only [liftM,MonadLift.monadLift,MonadLiftT.monadLift,F3S_Silent.lift_log,List.append_nil] using logs
#print axioms split
end AspisR1.F3S_SecondCommon
end
