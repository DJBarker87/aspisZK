import RawJ_MapSuccess
import RawJ_SemanticRead
import AuS1_Prepare
import AuS1_Suffix
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawJ_PrepareSemantic
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
    (s0 : erase (S1PrepareCode.prepare ops R B D pub proof hash input) = ok (.Ok p,scratch)) :
    ∃ (semantic y1 : Slice U8) (view : verifier.View) (sem : r1_semantic.Verified H),
      InstalledPreparation.sourceView proof semantic y1 = ok (.Ok view) ∧
      erase (S1SemanticCodeInstallation.code R B D pub view.semantic hash) = ok (.Ok sem) ∧
      erase (BorrowedClaimPrepared.closedPreparationCode D sem view hash input) = ok (.Ok p,scratch) ∧
      ∀ frame, Read (observe (run (S1SemanticCodeInstallation.code R B D pub view.semantic hash)).1) frame →
        Read (observe (run (S1PrepareCode.prepare ops R B D pub proof hash input)).1) frame := by
  let log := observe (run (S1PrepareCode.prepare ops R B D pub proof hash input)).1
  have inc0 : ∀ frame, Read (observe (run (S1PrepareCode.prepare ops R B D pub proof hash input)).1) frame →
      Read log frame := fun _ h => h
  change ∃ (semantic y1 : Slice U8) (view : verifier.View) (sem : r1_semantic.Verified H), _ ∧ _ ∧ _ ∧
    ∀ frame, Read (observe (run (S1SemanticCodeInstallation.code R B D pub view.semantic hash)).1) frame → Read log frame
  unfold S1PrepareCode.prepare at s0 inc0
  obtain ⟨i,h1,s1,sub1⟩ := AuS1_Suffix.right_read _ _ _ s0
  have inc1 := fun frame member => inc0 frame (sub1 frame member)
  obtain ⟨iy,h2,s2,sub2⟩ := AuS1_Suffix.right_read _ _ _ s1
  have inc2 := fun frame member => inc1 frame (sub2 frame member)
  obtain ⟨n,h3,s3,sub3⟩ := AuS1_Suffix.right_read _ _ _ s2
  have inc3 := fun frame member => inc2 frame (sub3 frame member)
  obtain ⟨allocated,h4,s4,sub4⟩ := AuS1_Suffix.right_read _ _ _ s3
  have inc4 := fun frame member => inc3 frame (sub4 frame member)
  obtain ⟨mapped,h5,s5,sub5⟩ := AuS1_Suffix.right_read _ _ _ s4
  have inc5 := fun frame member => inc4 frame (sub5 frame member)
  obtain ⟨cf,h6,s6,sub6⟩ := AuS1_Suffix.right_read _ _ _ s5
  have inc6 := fun frame member => inc5 frame (sub6 frame member)
  cases cf with
  | Break residual =>
    simp only [erase_bind,erase_lift,erase_pure] at s6
    repeat' first
      | (solve | cases s6)
      | uncase_result
      | head_reduce s6
      | split at s6
  | Continue val =>
    obtain ⟨deref,h7,s7,sub7⟩ := AuS1_Suffix.right_read _ _ _ s6
    have inc7 := fun frame member => inc6 frame (sub7 frame member)
    obtain ⟨split,h8,s8,sub8⟩ := AuS1_Suffix.right_read _ _ _ s7
    have inc8 := fun frame member => inc7 frame (sub8 frame member)
    obtain ⟨off0,h9,s9,sub9⟩ := AuS1_Suffix.right_read _ _ _ s8
    have inc9 := fun frame member => inc8 frame (sub9 frame member)
    obtain ⟨off1,h10,s10,sub10⟩ := AuS1_Suffix.right_read _ _ _ s9
    have inc10 := fun frame member => inc9 frame (sub10 frame member)
    obtain ⟨storedSemantic,h11,s11,sub11⟩ := AuS1_Suffix.right_read _ _ _ s10
    have inc11 := fun frame member => inc10 frame (sub11 frame member)
    obtain ⟨expandedSemantic,h12,s12,sub12⟩ := AuS1_Suffix.right_read _ _ _ s11
    have inc12 := fun frame member => inc11 frame (sub12 frame member)
    obtain ⟨cf1,h13,s13,sub13⟩ := AuS1_Suffix.right_read _ _ _ s12
    have inc13 := fun frame member => inc12 frame (sub13 frame member)
    cases cf1 with
    | Break residual =>
      simp only [erase_bind,erase_lift,erase_pure] at s13
      repeat' first
        | (solve | cases s13)
        | uncase_result
        | head_reduce s13
        | split at s13
    | Continue unit =>
      obtain ⟨off2,h14,s14,sub14⟩ := AuS1_Suffix.right_read _ _ _ s13
      have inc14 := fun frame member => inc13 frame (sub14 frame member)
      obtain ⟨storedY1,h15,s15,sub15⟩ := AuS1_Suffix.right_read _ _ _ s14
      have inc15 := fun frame member => inc14 frame (sub15 frame member)
      obtain ⟨expandedY1,h16,s16,sub16⟩ := AuS1_Suffix.right_read _ _ _ s15
      have inc16 := fun frame member => inc15 frame (sub16 frame member)
      obtain ⟨cf2,h17,s17,sub17⟩ := AuS1_Suffix.right_read _ _ _ s16
      have inc17 := fun frame member => inc16 frame (sub17 frame member)
      cases cf2 with
      | Break residual =>
        simp only [erase_bind,erase_lift,erase_pure] at s17
        repeat' first
          | (solve | cases s17)
          | uncase_result
          | head_reduce s17
          | split at s17
      | Continue unit1 =>
        obtain ⟨semantic,h18,s18,sub18⟩ := AuS1_Suffix.right_read _ _ _ s17
        have inc18 := fun frame member => inc17 frame (sub18 frame member)
        obtain ⟨y1,h19,s19,sub19⟩ := AuS1_Suffix.right_read _ _ _ s18
        have inc19 := fun frame member => inc18 frame (sub19 frame member)
        obtain ⟨viewResult,h20,s20,sub20⟩ := AuS1_Suffix.right_read _ _ _ s19
        have inc20 := fun frame member => inc19 frame (sub20 frame member)
        obtain ⟨cf3,h21,s21,sub21⟩ := AuS1_Suffix.right_read _ _ _ s20
        have inc21 := fun frame member => inc20 frame (sub21 frame member)
        cases cf3 with
        | Break residual =>
          simp only [erase_bind,erase_lift,erase_pure] at s21
          repeat' first
            | (solve | cases s21)
            | uncase_result
            | head_reduce s21
            | split at s21
        | Continue view =>
          obtain ⟨semanticResult,h22,s22,sub22⟩ := AuS1_Suffix.right_read _ _ _ s21
          have inc22 := fun frame member => inc21 frame (sub22 frame member)
          obtain ⟨mappedSemantic,h23,s23,sub23⟩ := AuS1_Suffix.right_read _ _ _ s22
          have inc23 := fun frame member => inc22 frame (sub23 frame member)
          obtain ⟨cf4,h24,s24,sub24⟩ := AuS1_Suffix.right_read _ _ _ s23
          have inc24 := fun frame member => inc23 frame (sub24 frame member)
          cases cf4 with
          | Break residual =>
            simp only [erase_bind,erase_lift,erase_pure] at s24
            repeat' first
              | (solve | cases s24)
              | uncase_result
              | head_reduce s24
              | split at s24
          | Continue sem =>
            obtain ⟨mark,h25,s25,sub25⟩ := AuS1_Suffix.right_read _ _ _ s24
            have inc25 := fun frame member => inc24 frame (sub25 frame member)
            rw [erase_lift] at h20 h21 h23 h24
            change core.result.Result.Insts.CoreOpsTry.branch viewResult = ok (.Continue view) at h21
            cases viewResult with
            | Err e => cases h21
            | Ok v =>
              have same : v = view := by simpa [core.result.Result.Insts.CoreOpsTry.branch] using h21
              subst v
              have sameResult := RawJ_MapSuccess.semantic D semanticResult mappedSemantic sem h23 h24
              rw [sameResult] at h22
              refine ⟨semantic,y1,view,sem,h20,h22,s25,?_⟩
              intro frame read
              exact inc21 frame (left_read _ _ _ s21 frame read)

#print axioms reached
end AspisR1.RawJ_PrepareSemantic
end
