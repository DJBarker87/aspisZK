import RawJ_ValidatedRead
import S1SemanticCodeBeginV1
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawJ_BeginC2
open Aeneas Aeneas.Std Result FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1PublicPreparation AspisR1PublicPreparation.PreparedHashCode AuS1_Suffix
attribute [local irreducible] S1SemanticCode.semanticValidated S1SemanticCode.begin5

theorem reached {H : Type} (D : aspis_core.Digest32 H) (pre : r1_wire.Prefix)
    (self after : r1_wire.SemanticTranscript H) (out : r1_wire.Challenges)
    (success : erase (S1SemanticCode.begin D pre self) = ok (.Ok out,after)) :
    ∃ (before2 after2 : r1_wire.SemanticTranscript H) (record : r1_wire.ValidatedRecord)
      (q : aspis_core.field.QM31),
      pre.validated_record 2#u8 = ok (.Ok record) ∧
      erase (S1SemanticCode.semanticValidated D before2 record) = ok (.Ok q,after2) ∧
      ∀ frame, Read (observe (run (S1SemanticCode.semanticValidated D before2 record)).1) frame →
        Read (observe (run (S1SemanticCode.begin D pre self)).1) frame := by
  let log := observe (run (S1SemanticCode.begin D pre self)).1
  have inc : ∀ frame, Read (observe (run (S1SemanticCode.begin D pre self)).1) frame → Read log frame := fun _ h => h
  change ∃ before2 after2 record q, _ ∧ _ ∧ ∀ frame, _ → Read log frame
  unfold S1SemanticCode.begin at success inc
  obtain ⟨r0,hr0,s1,sub1⟩ := right_read _ _ _ success
  have inc1 := fun frame member => inc frame (sub1 frame member)
  obtain ⟨cf2,hcf2,s2,sub2⟩ := right_read _ _ _ s1
  have inc2 := fun frame member => inc1 frame (sub2 frame member)
  cases cf2 with
  | Break residual =>
    simp only [erase_bind,erase_lift,erase_pure] at s2
    repeat' first | (solve | cases s2) | uncase_result | head_reduce s2 | split at s2
  | Continue vr0 =>
    obtain ⟨pair0,hp0,s3,sub3⟩ := right_read _ _ _ s2
    rcases pair0 with ⟨result0,tr0⟩
    have inc3 := fun frame member => inc2 frame (sub3 frame member)
    obtain ⟨cf4,hcf4,s4,sub4⟩ := right_read _ _ _ s3
    have inc4 := fun frame member => inc3 frame (sub4 frame member)
    cases cf4 with
    | Break residual =>
      simp only [erase_bind,erase_lift,erase_pure] at s4
      repeat' first | (solve | cases s4) | uncase_result | head_reduce s4 | split at s4
    | Continue q0 =>
      obtain ⟨r1,hr1,s5,sub5⟩ := right_read _ _ _ s4
      have inc5 := fun frame member => inc4 frame (sub5 frame member)
      obtain ⟨cf6,hcf6,s6,sub6⟩ := right_read _ _ _ s5
      have inc6 := fun frame member => inc5 frame (sub6 frame member)
      cases cf6 with
      | Break residual =>
        simp only [erase_bind,erase_lift,erase_pure] at s6
        repeat' first | (solve | cases s6) | uncase_result | head_reduce s6 | split at s6
      | Continue vr1 =>
        obtain ⟨pair1,hp1,s7,sub7⟩ := right_read _ _ _ s6
        rcases pair1 with ⟨result1,tr1⟩
        have inc7 := fun frame member => inc6 frame (sub7 frame member)
        obtain ⟨cf8,hcf8,s8,sub8⟩ := right_read _ _ _ s7
        have inc8 := fun frame member => inc7 frame (sub8 frame member)
        cases cf8 with
        | Break residual =>
          simp only [erase_bind,erase_lift,erase_pure] at s8
          repeat' first | (solve | cases s8) | uncase_result | head_reduce s8 | split at s8
        | Continue q1 =>
          obtain ⟨r2,hr2,s9,sub9⟩ := right_read _ _ _ s8
          have inc9 := fun frame member => inc8 frame (sub9 frame member)
          obtain ⟨cf10,hcf10,s10,sub10⟩ := right_read _ _ _ s9
          have inc10 := fun frame member => inc9 frame (sub10 frame member)
          cases cf10 with
          | Break residual =>
            simp only [erase_bind,erase_lift,erase_pure] at s10
            repeat' first | (solve | cases s10) | uncase_result | head_reduce s10 | split at s10
          | Continue vr2 =>
            obtain ⟨pair2,hp2,s11,sub11⟩ := right_read _ _ _ s10
            rcases pair2 with ⟨result2,tr2⟩
            have inc11 := fun frame member => inc10 frame (sub11 frame member)
            obtain ⟨cf12,hcf12,s12,sub12⟩ := right_read _ _ _ s11
            have inc12 := fun frame member => inc11 frame (sub12 frame member)
            cases cf12 with
            | Break residual =>
              simp only [erase_bind,erase_lift,erase_pure] at s12
              repeat' first | (solve | cases s12) | uncase_result | head_reduce s12 | split at s12
            | Continue q2 =>
              rw [erase_lift] at hr2 hcf10 hcf12
              cases r2 with
              | Err e => cases hcf10
              | Ok actual =>
                have same : actual = vr2 := by simpa [core.result.Result.Insts.CoreOpsTry.branch] using hcf10
                subst actual
                cases result2 with
                | Err e => cases hcf12
                | Ok actual =>
                  have same : actual = q2 := by simpa [core.result.Result.Insts.CoreOpsTry.branch] using hcf12
                  subst actual
                  refine ⟨tr1,tr2,vr2,q2,hr2,hp2,?_⟩
                  intro frame read
                  exact inc10 frame (left_read _ _ _ s10 frame read)

#print axioms reached
end AspisR1.RawJ_BeginC2
end
