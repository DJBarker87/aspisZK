import F3S_FirstTail
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
          change erase (SdkC_Source.dictionary hashv) ()
            (F3S_FirstTailCode.code base B std D hash publicBytes proof k p scratch)=ok (.Ok saved) at s7
          obtain ⟨root,acc,batch,writer,tailLog⟩ :=
            F3S_FirstTail.split base B std hashv D publicBytes proof k hash p scratch saved s7
          erw [tailLog] at logs
          exact ⟨zero,p,scratch,root,acc,hprepared,batch,writer,logs⟩

#print axioms split
end AspisR1.F3S_FirstSplice
end
