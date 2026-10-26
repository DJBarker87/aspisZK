import F3R_SdkPure
import F3R_Try
import GExq_FirstCode
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3S_FirstSplice
open Aeneas Aeneas.Std Result CheckpointBytes5Effect AspisR1CurrentCaller
local instance : MonadLift Result Code where monadLift := CheckpointBytes5Effect.liftResult
attribute [local irreducible] SdkD_PrepareLower.lower GExq_BatchSource.current GExp_FirstCode.writerCode

theorem split {Hash : Type} (base : Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (D : aspis_core.digest.Digest32 Hash)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (publicBytes proof : Slice U8) (k : Usize) (hash : Hash) (saved : alloc.vec.Vec U8)
    (success : erase (SdkC_Source.dictionary hashv) ()
      (GExq_FirstCode.code base B std hashv D pub publicBytes proof k hash)=ok (.Ok saved)) :
    ∃ (zero : aspis_core.field.wide_exact.WideExact) (p : verifier.Prepared)
      (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
      (root : Array U8 32#usize) (acc : verifier.Accumulator),
      erase (SdkC_Source.dictionary hashv) () (SdkD_PrepareLower.lower
        (SdkD_PrepareSource.code (Op5T_Concrete.current {base with op16:=Tx1Q_Install.writer})
          B std D pub proof hash (Array.repeat 29#usize zero)))=ok (.Ok p,scratch) ∧
      erase (SdkC_Source.dictionary hashv) () (GExq_BatchSource.current D hash proof p root)=ok (.Ok ()) ∧
      erase (SdkC_Source.dictionary hashv) () (GExp_FirstCode.writerCode p acc proof publicBytes)=ok saved ∧
      SdkC_Source.readLog (SdkC_Source.run hashv
        (GExq_FirstCode.code base B std hashv D pub publicBytes proof k hash) []).2=
      SdkC_Source.readLog (SdkC_Source.run hashv (SdkD_PrepareLower.lower
        (SdkD_PrepareSource.code (Op5T_Concrete.current {base with op16:=Tx1Q_Install.writer})
          B std D pub proof hash (Array.repeat 29#usize zero))) []).2 ++
        (SdkC_Source.readLog (SdkC_Source.run hashv (GExq_BatchSource.current D hash proof p root) []).2 ++
         SdkC_Source.readLog (SdkC_Source.run hashv (GExp_FirstCode.writerCode p acc proof publicBytes) []).2) := by
  unfold GExq_FirstCode.code at success ⊢
  by_cases bad : (k != compact.SPLIT)=true
  · simp only [bad,if_true,erase] at success
    cases success
  · simp only [bad,if_false] at success ⊢
    obtain ⟨shape,hs,s0,l0⟩ := F3R_SdkPure.right hashv _ _ _ success
    have logs := l0
    obtain ⟨cf,hcf,s1,l1⟩ := F3R_SdkPure.right hashv _ _ _ s0
    erw [l1] at logs
    cases cf with
    | Break residual =>
      simp only [erase_bind,erase_lift,erase_pure] at s1
      repeat' first | (solve | cases s1) | uncase_result | head_reduce s1 | split at s1
    | Continue value =>
      obtain ⟨scan,hscan,s2,l2⟩ := F3R_SdkPure.right hashv _ _ _ s1
      erw [l2] at logs
      obtain ⟨cfScan,hcfScan,s3,l3⟩ := F3R_SdkPure.right hashv _ _ _ s2
      erw [l3] at logs
      cases cfScan with
      | Break residual =>
        simp only [erase_bind,erase_lift,erase_pure] at s3
        repeat' first | (solve | cases s3) | uncase_result | head_reduce s3 | split at s3
      | Continue unit =>
        obtain ⟨mark,hmark,s4,l4⟩ := F3R_SdkPure.right hashv _ _ _ s3
        erw [l4] at logs
        obtain ⟨zero,hzero,s5,l5⟩ := F3R_SdkPure.right hashv _ _ _ s4
        erw [l5] at logs
        obtain ⟨prepared,hprepared,s6,l6⟩ := GExq_CodeTrace.success_bind hashv _ _ _ s5
        erw [l6] at logs
        rcases prepared with ⟨result,scratch⟩
        obtain ⟨cfPrepared,hcfPrepared,s7,l7⟩ := F3R_SdkPure.right hashv _ _ _ s6
        erw [l7] at logs
        cases cfPrepared with
        | Break residual =>
          simp only [erase_bind,erase_lift,erase_pure] at s7
          repeat' first | (solve | cases s7) | uncase_result | head_reduce s7 | split at s7
        | Continue p =>
          rw [F3R_Try.continued result p hcfPrepared] at hprepared
          obtain ⟨initial,h8,s8,l8⟩ := F3R_SdkPure.right hashv _ _ _ s7
          erw [l8] at logs
          obtain ⟨cfInitial,h9,s9,l9⟩ := F3R_SdkPure.right hashv _ _ _ s8
          erw [l9] at logs
          cases cfInitial with
          | Break residual => (simp only [erase_bind,erase_lift,erase_pure] at s9; repeat' first | (solve | cases s9) | uncase_result | head_reduce s9 | split at s9)
          | Continue initialAcc =>
            obtain ⟨markPrepare,h10,s10,l10⟩ := F3R_SdkPure.right hashv _ _ _ s9
            erw [l10] at logs
            obtain ⟨offRoot,h11,s11,l11⟩ := F3R_SdkPure.right hashv _ _ _ s10
            erw [l11] at logs
            obtain ⟨offRound,h12,s12,l12⟩ := F3R_SdkPure.right hashv _ _ _ s11
            erw [l12] at logs
            obtain ⟨view,h13,s13,l13⟩ := F3R_SdkPure.right hashv _ _ _ s12
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
            | Break residual => (simp only [erase_bind,erase_lift,erase_pure] at s17; repeat' first | (solve | cases s17) | uncase_result | head_reduce s17 | split at s17)
            | Continue batchUnit =>
              obtain ⟨markBatch,h18,s18,l18⟩ := F3R_SdkPure.right hashv _ _ _ s17
              erw [l18] at logs
              obtain ⟨queryResult,h19,s19,l19⟩ := F3R_SdkPure.right hashv _ _ _ s18
              erw [l19] at logs
              obtain ⟨cfQuery,h20,s20,l20⟩ := F3R_SdkPure.right hashv _ _ _ s19
              erw [l20] at logs
              cases cfQuery with
              | Break residual => (simp only [erase_bind,erase_lift,erase_pure] at s20; repeat' first | (solve | cases s20) | uncase_result | head_reduce s20 | split at s20)
              | Continue queryState =>
                obtain ⟨weightResult,h21,s21,l21⟩ := F3R_SdkPure.right hashv _ _ _ s20
                erw [l21] at logs
                obtain ⟨cfWeight,h22,s22,l22⟩ := F3R_SdkPure.right hashv _ _ _ s21
                erw [l22] at logs
                cases cfWeight with
                | Break residual => (simp only [erase_bind,erase_lift,erase_pure] at s22; repeat' first | (solve | cases s22) | uncase_result | head_reduce s22 | split at s22)
                | Continue weightState =>
                  obtain ⟨advanceResult,h23,s23,l23⟩ := F3R_SdkPure.right hashv _ _ _ s22
                  erw [l23] at logs
                  obtain ⟨cfAdvance,h24,s24,l24⟩ := F3R_SdkPure.right hashv _ _ _ s23
                  erw [l24] at logs
                  cases cfAdvance with
                  | Break residual => (simp only [erase_bind,erase_lift,erase_pure] at s24; repeat' first | (solve | cases s24) | uncase_result | head_reduce s24 | split at s24)
                  | Continue advance =>
                    rcases advance with ⟨a,pending⟩
                    obtain ⟨borrow,h25,s25,l25⟩ := F3R_SdkPure.right hashv _ _ _ s24
                    erw [l25] at logs
                    rcases borrow with ⟨weights,back⟩
                    obtain ⟨flushed,h26,s26,l26⟩ := F3R_SdkPure.right hashv _ _ _ s25
                    erw [l26] at logs
                    obtain ⟨written,h27,s27,l27⟩ := GExq_CodeTrace.success_bind hashv _ _ _ s26
                    erw [l27] at logs
                    obtain ⟨markWrite,h28,s28,l28⟩ := F3R_SdkPure.right hashv _ _ _ s27
                    erw [l28] at logs
                    have same : written=saved := core.result.Result.Ok.inj (Result.ok.inj s28)
                    subst written
                    have batch := F3R_Try.continued batchResult batchUnit h17
                    refine ⟨zero,p,scratch,root,_,hprepared,?_,h27,?_⟩
                    · simpa only [batch] using h16
                    · simpa only [SdkC_Source.run,SdkC_Source.readLog,List.filterMap_nil,List.append_nil] using logs

#print axioms split
end AspisR1.F3S_FirstSplice
end
