import RPz8_RawK_CodeHead
import RPz8_GExq_CodeTrace
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawK_FirstHead
open Aeneas Aeneas.Std Result AspisR1CurrentCaller CheckpointBytes5Effect GExq_CodeTrace
open FS2.Duplex
local instance : MonadLift Result Code where monadLift := liftResult

private theorem erase_liftM {A : Type} (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (r : Result A) : erase (SdkC_Source.dictionary hashv) () (liftM r : Code A) = r := by
  cases r <;> rfl

theorem first {Hash : Type} (base : Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : aspis_core.digest.Digest32 Hash)
    (law : ∀ h parts, D.digest h parts = hashv parts)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (publicBytes proof : Slice U8) (split : Usize) (hash : Hash) (saved : alloc.vec.Vec U8)
    (success : erase (SdkC_Source.dictionary hashv) ()
      (GExq_FirstCode.code base B std hashv D pub publicBytes proof split hash) = ok (.Ok saved)) :
    ∃ entry, RawK_CodeHead.head hashv (GExq_FirstCode.code base B std hashv D pub publicBytes proof split hash) = some entry ∧
      entry.1.head? = some 85 := by
  let log := RawK_CodeHead.head hashv (GExq_FirstCode.code base B std hashv D pub publicBytes proof split hash)
  have inc : ∀ entry, RawK_CodeHead.head hashv (GExq_FirstCode.code base B std hashv D pub publicBytes proof split hash) = some entry →
      log = some entry := fun _ h => h
  change ∃ entry, log = some entry ∧ _
  unfold GExq_FirstCode.code at success inc
  split at success
  · cases success
  · rename_i branch
    simp only [if_neg branch] at inc
    obtain ⟨r,hr,s1,sub1⟩ := RawK_CodeHead.right hashv _ _ _ success
    obtain ⟨cf,hcf,s2,sub2⟩ := RawK_CodeHead.right hashv _ _ _ s1
    cases cf with
    | Break residual =>
      simp only [erase_liftM] at s2
      repeat' first | (solve | cases s2) | uncase_result | head_reduce s2 | split at s2
    | Continue u =>
      obtain ⟨r1,hr1,s3,sub3⟩ := RawK_CodeHead.right hashv _ _ _ s2
      obtain ⟨cf1,hcf1,s4,sub4⟩ := RawK_CodeHead.right hashv _ _ _ s3
      cases cf1 with
      | Break residual =>
        simp only [erase_liftM] at s4
        repeat' first | (solve | cases s4) | uncase_result | head_reduce s4 | split at s4
      | Continue u1 =>
        obtain ⟨mark,hm,s5,sub5⟩ := RawK_CodeHead.right hashv _ _ _ s4
        obtain ⟨zero,hz,s6,sub6⟩ := RawK_CodeHead.right hashv _ _ _ s5
        obtain ⟨pair,hprep,s7,sub7⟩ := success_bind hashv _ _ _ s6
        obtain ⟨r2,scratch⟩ := pair
        obtain ⟨cf2,hcf2,s8,sub8⟩ := RawK_CodeHead.right hashv _ _ _ s7
        cases cf2 with
        | Break residual =>
          simp only [erase_liftM] at s8
          repeat' first | (solve | cases s8) | uncase_result | head_reduce s8 | split at s8
        | Continue p =>
          rw [erase_liftM] at hcf2
          cases r2 with
          | Err e => cases hcf2
          | Ok actual =>
            have same : actual = p := by simpa [core.result.Result.Insts.CoreOpsTry.branch] using hcf2
            subst actual
            obtain ⟨entry,head,tag⟩ := RawK_CodeHead.prepare
              (Op5T_Concrete.current {base with op16 := Tx1Q_Install.writer}) B std hashv D law
              pub proof hash p (Array.repeat 29#usize zero) scratch hprep
            have child := RawK_CodeHead.left hashv _ _ _ s6 entry head
            exact ⟨entry,inc entry (sub1 entry (sub2 entry (sub3 entry (sub4 entry (sub5 entry (sub6 entry child)))))),tag⟩

#print axioms erase_liftM
#print axioms first
end AspisR1.RawK_FirstHead
end
