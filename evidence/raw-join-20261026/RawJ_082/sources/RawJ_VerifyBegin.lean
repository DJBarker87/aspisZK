import RawJ_BeginC2
import RawJ_PublicRead
import S1SemanticCodeVerifyV1
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawJ_VerifyBegin
open Aeneas Aeneas.Std Result FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisR1PublicPreparation AspisR1PublicPreparation.PreparedHashCode AuS1_Suffix

theorem reached (F : S1SemanticCode.Finish) {H : Type} (D : aspis_core.Digest32 H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (input : Slice U8) (hash : H)
    (obs : Option (verifier.Phase → Result Unit)) (out : r1_semantic.Verified H)
    (success : erase (S1SemanticCode.verify F D pub input hash obs) = ok (.Ok out)) :
    ∃ (p : r1_wire.Prefix) (before after : r1_wire.SemanticTranscript H) (challenges : r1_wire.Challenges),
      PrefixAdapter.parseAccepted input = ok (.Ok p) ∧
      erase (S1SemanticCode.begin D p before) = ok (.Ok challenges,after) ∧
      ∀ frame, Read (observe (run (S1SemanticCode.begin D p before)).1) frame →
        Read (observe (run (S1SemanticCode.verify F D pub input hash obs)).1) frame := by
  let log := observe (run (S1SemanticCode.verify F D pub input hash obs)).1
  have inc : ∀ frame, Read (observe (run (S1SemanticCode.verify F D pub input hash obs)).1) frame →
      Read log frame := fun _ h => h
  change ∃ (p : r1_wire.Prefix) (before after : r1_wire.SemanticTranscript H) (challenges : r1_wire.Challenges),
    _ ∧ _ ∧ ∀ frame, _ → Read log frame
  unfold S1SemanticCode.verify at success inc
  obtain ⟨r,hr,s1,sub1⟩ := right_read _ _ _ success
  obtain ⟨cf,hcf,s2,sub2⟩ := right_read _ _ _ s1
  cases cf with
  | Break residual =>
    rw [erase_lift] at s2
    repeat' first | (solve | cases s2) | uncase_result | head_reduce s2 | split at s2
  | Continue p =>
    rw [erase_lift] at hr hcf
    cases r with
    | Err error => cases hcf
    | Ok parsed =>
      have same : parsed = p := by simpa [core.result.Result.Insts.CoreOpsTry.branch] using hcf
      subst parsed
      obtain ⟨mark,hm,s3,sub3⟩ := right_read _ _ _ s2
      obtain ⟨r1,hr1,s4,sub4⟩ := right_read _ _ _ s3
      obtain ⟨cf1,hcf1,s5,sub5⟩ := right_read _ _ _ s4
      cases cf1 with
      | Break residual =>
        rw [erase_lift] at s5
        repeat' first | (solve | cases s5) | uncase_result | head_reduce s5 | split at s5
      | Continue transcript =>
        rw [erase_lift] at hcf1
        cases r1 with
        | Err error => cases hcf1
        | Ok actual =>
          have same : actual = transcript := by simpa [core.result.Result.Insts.CoreOpsTry.branch] using hcf1
          subst actual
          obtain ⟨pair,hbegin,s6,sub6⟩ := right_read _ _ _ s5
          rcases pair with ⟨result,after⟩
          obtain ⟨cf2,hcf2,s7,sub7⟩ := right_read _ _ _ s6
          cases cf2 with
          | Break residual =>
            rw [erase_lift] at s7
            repeat' first | (solve | cases s7) | uncase_result | head_reduce s7 | split at s7
          | Continue challenges =>
            rw [erase_lift] at hcf2
            cases result with
            | Err e => cases hcf2
            | Ok actual =>
              have same : actual = challenges := by simpa [core.result.Result.Insts.CoreOpsTry.branch] using hcf2
              subst actual
              refine ⟨p,transcript,after,challenges,hr,hbegin,?_⟩
              intro frame read
              have member := left_read _ _ _ s5 frame read
              exact inc _ (sub1 _ (sub2 _ (sub3 _ (sub4 _ (sub5 _ member)))))

#print axioms reached
end AspisR1.RawJ_VerifyBegin
end
