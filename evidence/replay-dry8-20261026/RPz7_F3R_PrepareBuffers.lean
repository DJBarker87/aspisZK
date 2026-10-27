import RPz7_F3K_CodePure
import RPz7_F3R_Try
import S1PrepareBothBuffersV1
import RPz7_RawJ_MapSuccess
import RPz7_RawJ_SemanticRead
import RPz7_AuS1_Prepare
import RPz7_AuS1_Suffix
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3R_PrepareBuffers
open Aeneas Aeneas.Std Result
open FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1PublicPreparation.PreparedHashCode
open AspisR1CurrentCaller
attribute [local irreducible] S1SemanticCodeInstallation.code S1PrepareCode.prepare
  BorrowedClaimPrepared.closedPreparationCode InstalledPreparation.sourceView

 theorem reached (ops : Ops) (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    {H : Type} (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : H) (p : verifier.Prepared)
    (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (semanticLength : ∀ input output status updated,
      (BorrowedClaimPrepared.NativeBuffers.install (AspisS1ValuesOwnedInstallation.withValues ops) AspisS1ValuesOwnedInstallation.nativeValues R B).op10 input output=ok (status,updated) → updated.length=output.length)
    (valueLength : ∀ input output status updated,
      (BorrowedClaimPrepared.NativeBuffers.install (AspisS1ValuesOwnedInstallation.withValues ops) AspisS1ValuesOwnedInstallation.nativeValues R B).op11 input output=ok (status,updated) → updated.length=output.length)
    (s0 : erase (S1PrepareCode.prepare ops R B D pub proof hash input) = ok (.Ok p,scratch)) :
    ∃ (semantic y1 : Slice U8) (view : verifier.View) (sem : r1_semantic.Verified H),
      InstalledPreparation.sourceView proof semantic y1 = ok (.Ok view) ∧
      erase (S1SemanticCodeInstallation.code R B D pub view.semantic hash) = ok (.Ok sem) ∧
      erase (BorrowedClaimPrepared.closedPreparationCode D sem view hash input) = ok (.Ok p,scratch) ∧
      observe (run (S1PrepareCode.prepare ops R B D pub proof hash input)).1=
        observe (run (S1SemanticCodeInstallation.code R B D pub view.semantic hash)).1 ++
        observe (run (BorrowedClaimPrepared.closedPreparationCode D sem view hash input)).1 ∧
      ∃ (off0 off1 off2 : Usize) (stored initial expanded storedY1 initialY1 expandedY1 : Slice U8),
        compact.OFF_SEMANTIC (BorrowedClaimPrepared.NativeBuffers.install (AspisS1ValuesOwnedInstallation.withValues ops) AspisS1ValuesOwnedInstallation.nativeValues R B)=ok off0 ∧
        compact.OFF_Y1 (BorrowedClaimPrepared.NativeBuffers.install (AspisS1ValuesOwnedInstallation.withValues ops) AspisS1ValuesOwnedInstallation.nativeValues R B)=ok off1 ∧
        compact.OFF_INACTIVE (BorrowedClaimPrepared.NativeBuffers.install (AspisS1ValuesOwnedInstallation.withValues ops) AspisS1ValuesOwnedInstallation.nativeValues R B)=ok off2 ∧
        core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
          proof {start:=off0,«end»:=off1}=ok stored ∧
        (BorrowedClaimPrepared.NativeBuffers.install (AspisS1ValuesOwnedInstallation.withValues ops) AspisS1ValuesOwnedInstallation.nativeValues R B).op10 stored initial=ok (.Ok (),expanded) ∧
        core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
          proof {start:=off1,«end»:=off2}=ok storedY1 ∧
        (BorrowedClaimPrepared.NativeBuffers.install (AspisS1ValuesOwnedInstallation.withValues ops) AspisS1ValuesOwnedInstallation.nativeValues R B).op11 storedY1 initialY1=ok (.Ok (),expandedY1) ∧
        semantic=expanded ∧ y1=expandedY1 := by
  let log := observe (run (S1PrepareCode.prepare ops R B D pub proof hash input)).1
  have logs0 : log=observe (run (S1PrepareCode.prepare ops R B D pub proof hash input)).1 := rfl
  change ∃ (semantic y1 : Slice U8) (view : verifier.View) (sem : r1_semantic.Verified H), _ ∧ _ ∧ _ ∧
    log=observe (run (S1SemanticCodeInstallation.code R B D pub view.semantic hash)).1 ++
      observe (run (BorrowedClaimPrepared.closedPreparationCode D sem view hash input)).1 ∧ _
  unfold S1PrepareCode.prepare at s0 logs0
  obtain ⟨i,h1,s1,sub1⟩ := F3K_CodePure.invert _ _ _ s0
  have logs1 := logs0.trans sub1
  obtain ⟨iy,h2,s2,sub2⟩ := F3K_CodePure.invert _ _ _ s1
  have logs2 := logs1.trans sub2
  obtain ⟨n,h3,s3,sub3⟩ := F3K_CodePure.invert _ _ _ s2
  have logs3 := logs2.trans sub3
  obtain ⟨allocated,h4,s4,sub4⟩ := F3K_CodePure.invert _ _ _ s3
  have logs4 := logs3.trans sub4
  obtain ⟨mapped,h5,s5,sub5⟩ := F3K_CodePure.invert _ _ _ s4
  have logs5 := logs4.trans sub5
  obtain ⟨cf,h6,s6,sub6⟩ := F3K_CodePure.invert _ _ _ s5
  have logs6 := logs5.trans sub6
  cases cf with
  | Break residual =>
    simp only [erase_bind,erase_lift,erase_pure] at s6
    repeat' first
      | (solve | cases s6)
      | uncase_result
      | head_reduce s6
      | split at s6
  | Continue val =>
    obtain ⟨deref,h7,s7,sub7⟩ := F3K_CodePure.invert _ _ _ s6
    have logs7 := logs6.trans sub7
    obtain ⟨split,h8,s8,sub8⟩ := F3K_CodePure.invert _ _ _ s7
    have logs8 := logs7.trans sub8
    obtain ⟨off0,h9,s9,sub9⟩ := F3K_CodePure.invert _ _ _ s8
    have logs9 := logs8.trans sub9
    obtain ⟨off1,h10,s10,sub10⟩ := F3K_CodePure.invert _ _ _ s9
    have logs10 := logs9.trans sub10
    obtain ⟨storedSemantic,h11,s11,sub11⟩ := F3K_CodePure.invert _ _ _ s10
    have logs11 := logs10.trans sub11
    obtain ⟨expandedSemantic,h12,s12,sub12⟩ := F3K_CodePure.invert _ _ _ s11
    have logs12 := logs11.trans sub12
    obtain ⟨cf1,h13,s13,sub13⟩ := F3K_CodePure.invert _ _ _ s12
    have logs13 := logs12.trans sub13
    cases cf1 with
    | Break residual =>
      simp only [erase_bind,erase_lift,erase_pure] at s13
      repeat' first
        | (solve | cases s13)
        | uncase_result
        | head_reduce s13
        | split at s13
    | Continue unit =>
      obtain ⟨off2,h14,s14,sub14⟩ := F3K_CodePure.invert _ _ _ s13
      have logs14 := logs13.trans sub14
      obtain ⟨storedY1,h15,s15,sub15⟩ := F3K_CodePure.invert _ _ _ s14
      have logs15 := logs14.trans sub15
      obtain ⟨expandedY1,h16,s16,sub16⟩ := F3K_CodePure.invert _ _ _ s15
      have logs16 := logs15.trans sub16
      obtain ⟨cf2,h17,s17,sub17⟩ := F3K_CodePure.invert _ _ _ s16
      have logs17 := logs16.trans sub17
      cases cf2 with
      | Break residual =>
        simp only [erase_bind,erase_lift,erase_pure] at s17
        repeat' first
          | (solve | cases s17)
          | uncase_result
          | head_reduce s17
          | split at s17
      | Continue unit1 =>
        obtain ⟨semantic,h18,s18,sub18⟩ := F3K_CodePure.invert _ _ _ s17
        have logs18 := logs17.trans sub18
        obtain ⟨y1,h19,s19,sub19⟩ := F3K_CodePure.invert _ _ _ s18
        have logs19 := logs18.trans sub19
        obtain ⟨viewResult,h20,s20,sub20⟩ := F3K_CodePure.invert _ _ _ s19
        have logs20 := logs19.trans sub20
        obtain ⟨cf3,h21,s21,sub21⟩ := F3K_CodePure.invert _ _ _ s20
        have logs21 := logs20.trans sub21
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
          have observed22 := congrArg observe sub22
          rw [AuS1_Trace.observe_append] at observed22
          have logs22 := logs21.trans observed22
          obtain ⟨mappedSemantic,h23,s23,sub23⟩ := F3K_CodePure.invert _ _ _ s22
          have logs23 := logs22.trans (congrArg (List.append _) sub23)
          obtain ⟨cf4,h24,s24,sub24⟩ := F3K_CodePure.invert _ _ _ s23
          have logs24 := logs23.trans (congrArg (List.append _) sub24)
          cases cf4 with
          | Break residual =>
            simp only [erase_bind,erase_lift,erase_pure] at s24
            repeat' first
              | (solve | cases s24)
              | uncase_result
              | head_reduce s24
              | split at s24
          | Continue sem =>
            obtain ⟨mark,h25,s25,sub25⟩ := F3K_CodePure.invert _ _ _ s24
            have logs25 := logs24.trans (congrArg (List.append _) sub25)
            change core.result.Result.Insts.CoreOpsTry.branch viewResult = ok (.Continue view) at h21
            cases viewResult with
            | Err e => cases h21
            | Ok v =>
              have same : v = view := by simpa [core.result.Result.Insts.CoreOpsTry.branch] using h21
              subst v
              have sameResult := RawJ_MapSuccess.semantic D semanticResult mappedSemantic sem h23 h24
              rw [sameResult] at h22
              have status1 := F3R_Try.continued expandedSemantic.1 unit h13
              have status2 := F3R_Try.continued expandedY1.1 unit1 h17
              cases unit
              cases unit1
              have pair1 : expandedSemantic=(.Ok (),expandedSemantic.2) := Prod.ext status1 rfl
              have pair2 : expandedY1=(.Ok (),expandedY1.2) := Prod.ext status2 rfl
              have call1 := h12.trans (congrArg ok pair1)
              have call2 := h16.trans (congrArg ok pair2)
              have hderef := Result.ok.inj h7
              have sameSemantic := AspisS1PrepareBufferRecombine.semantic_recombined val deref split i
                expandedSemantic.2 expandedY1.2 semantic h7 h8
                (semanticLength _ _ _ _ call1) (valueLength _ _ _ _ call2) h18
              have sameY1 := AspisS1PrepareBufferRecombine.y1_recombined val deref split i
                expandedSemantic.2 expandedY1.2 y1 h7 h8
                (semanticLength _ _ _ _ call1) (valueLength _ _ _ _ call2) h19
              exact ⟨semantic,y1,view,sem,h20,h22,s25,logs25,
                off0,off1,off2,storedSemantic,split.1.1,expandedSemantic.2,storedY1,split.1.2,expandedY1.2,
                h9,h10,h14,h11,call1,h15,call2,sameSemantic,sameY1⟩

#print axioms reached
end AspisR1.F3R_PrepareBuffers
end
