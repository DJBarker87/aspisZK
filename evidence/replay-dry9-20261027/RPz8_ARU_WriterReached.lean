import RPz8_GExq_PrepareFrame
import RPz8_ARU_WriterHeader
import RPz8_GExq_CodeTrace
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARU_WriterReached
open Aeneas Aeneas.Std Result AspisR1CurrentCaller CheckpointBytes5Effect GExq_CodeTrace
open FS2.Duplex
local instance : MonadLift Result Code where monadLift := liftResult

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
    ∃ (p : verifier.Prepared) (a : verifier.Accumulator),
      erase (SdkC_Source.dictionary hashv) () (GExp_FirstCode.writerCode p a proof publicBytes) = ok saved ∧
      ∀ frame, Read (SdkC_Source.readLog (SdkC_Source.run hashv
        (GExp_FirstCode.writerCode p a proof publicBytes) []).2) frame →
        Read (SdkC_Source.readLog (SdkC_Source.run hashv
          (GExq_FirstCode.code base B std hashv D pub publicBytes proof split hash) []).2) frame := by
  let log := SdkC_Source.readLog (SdkC_Source.run hashv (GExq_FirstCode.code base B std hashv D pub publicBytes proof split hash) []).2
  have inc : ∀ frame, Read (SdkC_Source.readLog (SdkC_Source.run hashv
      (GExq_FirstCode.code base B std hashv D pub publicBytes proof split hash) []).2) frame → Read log frame := fun _ h => h
  change ∃ p a, _ ∧ ∀ frame, _ → Read log frame
  unfold GExq_FirstCode.code at success inc
  split at success
  · cases success
  · rename_i branch
    simp only [if_neg branch] at inc
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
        obtain ⟨pair,hprep,s7,sub7⟩ := right_read hashv _ _ _ s6
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
            obtain ⟨r3,h9,s9,sub9⟩ := right_read hashv _ _ _ s8
            obtain ⟨cf3,h10,s10,sub10⟩ := right_read hashv _ _ _ s9
            cases cf3 with
            | Break residual =>
              simp only [erase_liftM] at s10
              repeat' first | (solve | cases s10) | uncase_result | head_reduce s10 | split at s10
            | Continue acc =>
              obtain ⟨mark3,h11,s11,sub11⟩ := right_read hashv _ _ _ s10
              obtain ⟨i,h12,s12,sub12⟩ := right_read hashv _ _ _ s11
              obtain ⟨i1,h13,s13,sub13⟩ := right_read hashv _ _ _ s12
              obtain ⟨slice0,h14,s14,sub14⟩ := right_read hashv _ _ _ s13
              obtain ⟨r4,h15,s15,sub15⟩ := right_read hashv _ _ _ s14
              obtain ⟨folded,h16,s16,sub16⟩ := right_read hashv _ _ _ s15
              obtain ⟨r5,h17,s17,sub17⟩ := right_read hashv _ _ _ s16
              obtain ⟨cf4,h18,s18,sub18⟩ := right_read hashv _ _ _ s17
              cases cf4 with
              | Break residual =>
                simp only [erase_liftM] at s18
                repeat' first | (solve | cases s18) | uncase_result | head_reduce s18 | split at s18
              | Continue u4 =>
                obtain ⟨mark4,h19,s19,sub19⟩ := right_read hashv _ _ _ s18
                obtain ⟨r6,h20,s20,sub20⟩ := right_read hashv _ _ _ s19
                obtain ⟨cf5,h21,s21,sub21⟩ := right_read hashv _ _ _ s20
                cases cf5 with
                | Break residual =>
                  simp only [erase_liftM] at s21
                  repeat' first | (solve | cases s21) | uncase_result | head_reduce s21 | split at s21
                | Continue geoValue =>
                  obtain ⟨r7,h22,s22,sub22⟩ := right_read hashv _ _ _ s21
                  obtain ⟨cf6,h23,s23,sub23⟩ := right_read hashv _ _ _ s22
                  cases cf6 with
                  | Break residual =>
                    simp only [erase_liftM] at s23
                    repeat' first | (solve | cases s23) | uncase_result | head_reduce s23 | split at s23
                  | Continue batchValue =>
                    obtain ⟨r8,h24,s24,sub24⟩ := right_read hashv _ _ _ s23
                    obtain ⟨cf7,h25,s25,sub25⟩ := right_read hashv _ _ _ s24
                    cases cf7 with
                    | Break residual =>
                      simp only [erase_liftM] at s25
                      repeat' first | (solve | cases s25) | uncase_result | head_reduce s25 | split at s25
                    | Continue pairFinal =>
                      rcases pairFinal with ⟨accFinal,pending⟩
                      obtain ⟨mutPair,h26,s26,sub26⟩ := right_read hashv _ _ _ s25
                      rcases mutPair with ⟨mutWeights,back⟩
                      obtain ⟨written,h27,s27,sub27⟩ := right_read hashv _ _ _ s26
                      obtain ⟨bytes,h28,s28,sub28⟩ := right_read hashv _ _ _ s27
                      have bytesEq : bytes = saved := by
                        simpa only [verifier.mark,erase_bind,erase_liftM,erase_pure,bind_tc_ok] using
                          core.result.Result.Ok.inj (Result.ok.inj s28)
                      subst bytes
                      refine ⟨p,{accFinal with weights := back written},h28,?_⟩
                      intro frame member
                      have child := left_read hashv _ _ _ s27 frame member
                      exact inc frame (sub1 frame (sub2 frame (sub3 frame (sub4 frame (sub5 frame (sub6 frame (sub7 frame (sub8 frame (sub9 frame (sub10 frame (sub11 frame (sub12 frame (sub13 frame (sub14 frame (sub15 frame (sub16 frame (sub17 frame (sub18 frame (sub19 frame (sub20 frame (sub21 frame (sub22 frame (sub23 frame (sub24 frame (sub25 frame (sub26 frame (sub27 frame child)))))))))))))))))))))))))))

#print axioms erase_liftM
#print axioms reached
end AspisR1.ARU_WriterReached
end
