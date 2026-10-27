import GExq_PrepareFrame
import GExq_CodeTrace
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExq_FirstFrame
open Aeneas Aeneas.Std Result AspisR1CurrentCaller CheckpointBytes5Effect GExq_CodeTrace
open FS2.Duplex

private theorem erase_liftM {A : Type} (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (r : Result A) : erase (SdkC_Source.dictionary hashv) () (liftM r : Code A) = r := by
  cases r <;> rfl

theorem reached {Hash : Type} (base : Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : aspis_core.digest.Digest32 Hash)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (publicBytes proof : Slice U8) (split : Usize) (hash : Hash) (saved : alloc.vec.Vec U8)
    (success : erase (SdkC_Source.dictionary hashv) ()
      (GExq_FirstCode.code base B std hashv D pub publicBytes proof split hash) = ok (.Ok saved)) :
    ∃ (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize) (p : verifier.Prepared),
      erase (SdkC_Source.dictionary hashv) () (SdkD_PrepareLower.lower (SdkD_PrepareSource.code
        (Op5T_Concrete.current {base with op16 := Tx1Q_Install.writer}) B std D pub proof hash input)) =
        ok (.Ok p,scratch) ∧
      ∀ frame, Read (SdkC_Source.readLog (SdkC_Source.run hashv (SdkD_PrepareLower.lower
        (SdkD_PrepareSource.code (Op5T_Concrete.current {base with op16 := Tx1Q_Install.writer}) B std D pub proof hash input)) []).2) frame →
        Read (SdkC_Source.readLog (SdkC_Source.run hashv
          (GExq_FirstCode.code base B std hashv D pub publicBytes proof split hash) []).2) frame := by
  let log := SdkC_Source.readLog (SdkC_Source.run hashv (GExq_FirstCode.code base B std hashv D pub publicBytes proof split hash) []).2
  have inc : ∀ frame, Read (SdkC_Source.readLog (SdkC_Source.run hashv
      (GExq_FirstCode.code base B std hashv D pub publicBytes proof split hash) []).2) frame → Read log frame := fun _ h => h
  change ∃ input scratch p, _ ∧ ∀ frame, _ → Read log frame
  unfold GExq_FirstCode.code at success inc
  split at success
  · cases success
  · simp only [↓reduceIte] at inc
    obtain ⟨r,hr,s1,sub1⟩ := right_read hashv _ _ _ success
    obtain ⟨cf,hcf,s2,sub2⟩ := right_read hashv _ _ _ s1
    cases cf with
    | Break residual =>
      simp only [erase_liftM] at s2
      repeat' first | (solve | cases s2) | uncase_result | head_reduce s2 | split at s2
    | Continue u =>
      obtain ⟨r1,hr1,s3,sub3⟩ := right_read hashv _ _ _ s2
      obtain ⟨cf1,hcf1,s4,sub4⟩ := right_read hashv _ _ _ s3
      cases cf1 with
      | Break residual =>
        simp only [erase_liftM] at s4
        repeat' first | (solve | cases s4) | uncase_result | head_reduce s4 | split at s4
      | Continue u1 =>
        obtain ⟨mark,hm,s5,sub5⟩ := right_read hashv _ _ _ s4
        obtain ⟨zero,hz,s6,sub6⟩ := right_read hashv _ _ _ s5
        obtain ⟨pair,hprep,s7,sub7⟩ := success_bind hashv _ _ _ s6
        obtain ⟨r2,scratch⟩ := pair
        obtain ⟨cf2,hcf2,s8,sub8⟩ := right_read hashv _ _ _ s7
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
            refine ⟨Array.repeat 29#usize zero,scratch,p,hprep,?_⟩
            intro frame member
            have child := left_read hashv _ _ _ s6 frame member
            exact inc frame (sub1 frame (sub2 frame (sub3 frame (sub4 frame (sub5 frame (sub6 frame child))))))

#print axioms erase_liftM
#print axioms reached
end AspisR1.GExq_FirstFrame
end
