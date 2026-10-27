import RPz7_RawK_PublicHead
import RPz7_S1SemanticCodeVerifyV1
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawK_VerifyHead
open Aeneas Aeneas.Std Result FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisR1PublicPreparation AspisR1PublicPreparation.PreparedHashCode AuS1_Suffix

theorem first (F : S1SemanticCode.Finish) {H : Type} (D : aspis_core.Digest32 H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (input : Slice U8) (hash : H)
    (obs : Option (RPz7_PhaseIso.Phase → Result Unit)) (out : r1_semantic.Verified H)
    (success : erase (S1SemanticCode.verify F D pub input hash obs) = ok (.Ok out)) :
    ∃ entry, RawK_Head.head (S1SemanticCode.verify F D pub input hash obs) = some entry ∧
      entry.1.head? = some 85 := by
  let log := RawK_Head.head (S1SemanticCode.verify F D pub input hash obs)
  have inc : ∀ entry, RawK_Head.head (S1SemanticCode.verify F D pub input hash obs) = some entry →
      log = some entry := fun _ h => h
  change ∃ entry, log = some entry ∧ _
  unfold S1SemanticCode.verify at success inc
  obtain ⟨r,hr,s1,sub1⟩  := RawK_Head.right _ _ _ success
  obtain ⟨cf,hcf,s2,sub2⟩  := RawK_Head.right _ _ _ s1
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
      obtain ⟨mark,hm,s3,sub3⟩  := RawK_Head.right _ _ _ s2
      obtain ⟨r1,hr1,s4,sub4⟩ := AuS1_Trace.success_bind _ _ _ s3
      obtain ⟨cf1,hcf1,s5,sub5⟩  := RawK_Head.right _ _ _ s4
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
          obtain ⟨entry,read,tag⟩ := RawK_PublicHead.first D hash pub p.c1_root transcript hr1
          have member := RawK_Head.left _ _ _ s3 entry read
          exact ⟨entry,inc _ (sub1 _ (sub2 _ (sub3 _ member))),tag⟩

#print axioms first
end AspisR1.RawK_VerifyHead
end
