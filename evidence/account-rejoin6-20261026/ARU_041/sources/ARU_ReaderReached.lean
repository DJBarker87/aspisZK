import ARU_ReaderHeader
import GExq_SecondCode
import GExq_CodeTrace
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARU_ReaderReached
open Aeneas Aeneas.Std Result VTop_Stages CheckpointBytes5Effect GExq_CodeTrace
local instance : MonadLift Result Code where monadLift := liftResult

private theorem erase_liftM {A : Type} (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (r : Result A) : erase (SdkC_Source.dictionary hashv) () (liftM r : Code A) = r := by
  cases r <;> rfl

theorem reached {Hash : Type} (base : Ops) (reserved : Bool)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash) (pub proof ck : Slice U8)
    (success : erase (SdkC_Source.dictionary hashv) ()
      (GExq_SecondCode.code base reserved hashv D pub proof ck hash) = ok (.Ok ())) :
    ∃ p a, erase (SdkC_Source.dictionary hashv) ()
      (GExq_RetainedReader.code reserved ck proof pub .S2) = ok (.Ok (p,a)) := by
  unfold GExq_SecondCode.code at success
  obtain ⟨r,hr,s1,sub1⟩ := right_read hashv _ _ _ success
  obtain ⟨cf,hcf,s2,sub2⟩ := right_read hashv _ _ _ s1
  cases cf with
  | Break residual =>
    simp only [erase_liftM] at s2
    repeat' first | (solve | cases s2) | uncase_result | head_reduce s2 | split at s2
  | Continue u =>
    obtain ⟨mark,hm,s3,sub3⟩ := right_read hashv _ _ _ s2
    unfold GExq_SecondCode.common at s3
    obtain ⟨reader,called,s4,sub4⟩ := right_read hashv _ _ _ s3
    obtain ⟨cf2,hcf2,s5,sub5⟩ := right_read hashv _ _ _ s4
    cases cf2 with
    | Break residual =>
      simp only [erase_liftM] at s5
      repeat' first | (solve | cases s5) | uncase_result | head_reduce s5 | split at s5
    | Continue pair =>
      rw [erase_liftM] at hcf2
      cases reader with
      | Err e => cases hcf2
      | Ok actual =>
        rcases actual with ⟨p,a⟩
        exact ⟨p,a,called⟩

#print axioms erase_liftM
#print axioms reached
end AspisR1.ARU_ReaderReached
end
