import F3Q_PreparePure
import AuS1_Prepare
import AuS1_Suffix
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3Q_PrepareSplit
open Aeneas Aeneas.Std Result
open FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1PublicPreparation.PreparedHashCode
open AspisR1CurrentCaller

 theorem reached (ops : Ops) (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    {H : Type} (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : H) (p : verifier.Prepared)
    (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (s0 : erase (S1PrepareCode.prepare ops R B D pub proof hash input) = ok (.Ok p,scratch)) :
    ∃ (semantic y1 : Slice U8) (view : verifier.View) (sem : r1_semantic.Verified H),
      InstalledPreparation.sourceView proof semantic y1 = ok (.Ok view) ∧
      erase (BorrowedClaimPrepared.closedPreparationCode D sem view hash input) = ok (.Ok p,scratch) ∧
      observe (run (S1PrepareCode.prepare ops R B D pub proof hash input)).1=
        observe (run (S1SemanticCodeInstallation.code R B D pub view.semantic hash)).1 ++
        observe (run (BorrowedClaimPrepared.closedPreparationCode D sem view hash input)).1 := by
  unfold S1PrepareCode.prepare at s0
  obtain ⟨i,h1,s1,sub1⟩ := F3Q_PreparePure.right _ _ _ s0
  obtain ⟨iy,h2,s2,sub2⟩ := F3Q_PreparePure.right _ _ _ s1
  obtain ⟨n,h3,s3,sub3⟩ := F3Q_PreparePure.right _ _ _ s2
  obtain ⟨allocated,h4,s4,sub4⟩ := F3Q_PreparePure.right _ _ _ s3
  obtain ⟨mapped,h5,s5,sub5⟩ := F3Q_PreparePure.right _ _ _ s4
  obtain ⟨cf,h6,s6,sub6⟩ := F3Q_PreparePure.right _ _ _ s5
  cases cf with
  | Break residual =>
    simp only [erase_bind,erase_lift,erase_pure] at s6
    repeat' first
      | (solve | cases s6)
      | uncase_result
      | head_reduce s6
      | split at s6
  | Continue val =>
    obtain ⟨deref,h7,s7,sub7⟩ := F3Q_PreparePure.right _ _ _ s6
    obtain ⟨split,h8,s8,sub8⟩ := F3Q_PreparePure.right _ _ _ s7
    obtain ⟨off0,h9,s9,sub9⟩ := F3Q_PreparePure.right _ _ _ s8
    obtain ⟨off1,h10,s10,sub10⟩ := F3Q_PreparePure.right _ _ _ s9
    obtain ⟨storedSemantic,h11,s11,sub11⟩ := F3Q_PreparePure.right _ _ _ s10
    obtain ⟨expandedSemantic,h12,s12,sub12⟩ := F3Q_PreparePure.right _ _ _ s11
    obtain ⟨cf1,h13,s13,sub13⟩ := F3Q_PreparePure.right _ _ _ s12
    cases cf1 with
    | Break residual =>
      simp only [erase_bind,erase_lift,erase_pure] at s13
      repeat' first
        | (solve | cases s13)
        | uncase_result
        | head_reduce s13
        | split at s13
    | Continue unit =>
      obtain ⟨off2,h14,s14,sub14⟩ := F3Q_PreparePure.right _ _ _ s13
      obtain ⟨storedY1,h15,s15,sub15⟩ := F3Q_PreparePure.right _ _ _ s14
      obtain ⟨expandedY1,h16,s16,sub16⟩ := F3Q_PreparePure.right _ _ _ s15
      obtain ⟨cf2,h17,s17,sub17⟩ := F3Q_PreparePure.right _ _ _ s16
      cases cf2 with
      | Break residual =>
        simp only [erase_bind,erase_lift,erase_pure] at s17
        repeat' first
          | (solve | cases s17)
          | uncase_result
          | head_reduce s17
          | split at s17
      | Continue unit1 =>
        obtain ⟨semantic,h18,s18,sub18⟩ := F3Q_PreparePure.right _ _ _ s17
        obtain ⟨y1,h19,s19,sub19⟩ := F3Q_PreparePure.right _ _ _ s18
        obtain ⟨viewResult,h20,s20,sub20⟩ := F3Q_PreparePure.right _ _ _ s19
        obtain ⟨cf3,h21,s21,sub21⟩ := F3Q_PreparePure.right _ _ _ s20
        cases cf3 with
        | Break residual =>
          simp only [erase_bind,erase_lift,erase_pure] at s21
          repeat' first
            | (solve | cases s21)
            | uncase_result
            | head_reduce s21
            | split at s21
        | Continue view =>
          obtain ⟨semanticResult,h22,s22,sub22⟩ := AuS1_Trace.success_bind _ _ _ s21
          obtain ⟨mappedSemantic,h23,s23,sub23⟩ := F3Q_PreparePure.right _ _ _ s22
          obtain ⟨cf4,h24,s24,sub24⟩ := F3Q_PreparePure.right _ _ _ s23
          cases cf4 with
          | Break residual =>
            simp only [erase_bind,erase_lift,erase_pure] at s24
            repeat' first
              | (solve | cases s24)
              | uncase_result
              | head_reduce s24
              | split at s24
          | Continue sem =>
            obtain ⟨mark,h25,s25,sub25⟩ := F3Q_PreparePure.right _ _ _ s24
            have prefixLog := sub1.trans (sub2.trans (sub3.trans (sub4.trans (sub5.trans (sub6.trans
              (sub7.trans (sub8.trans (sub9.trans (sub10.trans (sub11.trans (sub12.trans (sub13.trans
              (sub14.trans (sub15.trans (sub16.trans (sub17.trans (sub18.trans (sub19.trans (sub20.trans sub21)))))))))))))))))))
            have suffixLog := sub23.trans (sub24.trans sub25)
            have logs := prefixLog.trans (sub22.trans (congrArg (List.append _) suffixLog))
            refine ⟨semantic,y1,view,sem,?_,s25,?_⟩
            ·
              change core.result.Result.Insts.CoreOpsTry.branch viewResult = ok (.Continue view) at h21
              cases viewResult with
              | Err e => cases h21
              | Ok v =>
                have same : v = view := by simpa [core.result.Result.Insts.CoreOpsTry.branch] using h21
                subst v
                exact h20

            · exact (congrArg observe logs).trans (AuS1_Trace.observe_append _ _)

#print axioms reached
end AspisR1.F3Q_PrepareSplit
end
