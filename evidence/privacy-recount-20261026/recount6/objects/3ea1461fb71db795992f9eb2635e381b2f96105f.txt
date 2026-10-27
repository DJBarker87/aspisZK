import R1Z.ProverRwEffectPrefix
import R1Z.ProverRwEffectNonzero

/-! Regression on the actual factored source continuation, with four explicit
transparent-wrapper entries installed. This is not native effect adequacy. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwEffectRegression
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open ProverRwEffectSource ProverRwEffectTape ProverRwEffectPrefix
variable [ExternalTypes]

theorem constant_after (ops : ExternalFuns) (nonce : Array U8 32#usize) (retry : Usize)
    (byte : U8) (stable : byte ||| byte = byte) (initial : (0#u8) ||| byte = byte) :
    @after _ (install ops) nonce retry back
      (.Ok (),Array.to_slice (Array.repeat 64#usize byte)) =
      if byte != 0#u8 then .ok (.done (.Ok ⟨nonce,Array.repeat 32#usize byte,Array.repeat 32#usize byte⟩))
      else .ok (.cont (Usize.wrapping_add retry 1#usize)) := by
  letI : ExternalFuns := install ops
  change (do
    let b ← aspis_prover.state_only_entropy.entropy_nonzero32 (Array.repeat 32#usize byte)
    if b then do
      let b1 ← aspis_prover.state_only_entropy.entropy_nonzero32 (Array.repeat 32#usize byte)
      if b1 then .ok (.done (.Ok ⟨nonce,Array.repeat 32#usize byte,Array.repeat 32#usize byte⟩))
      else .ok (.cont (Usize.wrapping_add retry 1#usize))
    else .ok (.cont (Usize.wrapping_add retry 1#usize)) : Result Outcome) = _
  rw [ProverRwEffectNonzero.nonzero_repeat byte stable initial]
  simp only [bind_tc_ok]
  split <;> simp_all only [bind_tc_ok,if_true,if_false]


theorem after_zero (ops : ExternalFuns) (nonce : Array U8 32#usize) (retry : Usize) :
    @after _ (install ops) nonce retry back (.Ok (),ProverRwEntropyObstruction.zeroInput) =
      .ok (.cont (Usize.wrapping_add retry 1#usize)) := by
  exact constant_after ops nonce retry 0#u8 (by rfl) (by rfl)

theorem after_one (ops : ExternalFuns) (nonce : Array U8 32#usize) (retry : Usize) :
    @after _ (install ops) nonce retry back (.Ok (),ProverRwEntropyObstruction.oneOutput) =
      .ok (.done (.Ok ⟨nonce,Array.repeat 32#usize 1#u8,Array.repeat 32#usize 1#u8⟩)) := by
  exact constant_after ops nonce retry 1#u8 (by rfl) (by rfl)

theorem add_zero_one : Usize.wrapping_add 0#usize 1#usize = 1#usize := by
  apply UScalar.eq_of_val_eq
  rw [Usize.wrapping_add_val_eq]
  change 1 % UScalar.size .Usize = 1
  exact Nat.mod_eq_of_lt (1#usize).hSize

/-- Two iterations of the factored actual source body. The result and both
ordered fill calls are explicit; no retry/success premise is assumed. -/
theorem zero_then_one (ops : ExternalFuns) (nonce : Array U8 32#usize)
    (rest : List (Result Reply)) (reads : List (Slice U8 × Result Reply)) :
    letI : ExternalFuns := install ops
    let zero := ProverRwEntropyObstruction.zeroInput
    let one := ProverRwEntropyObstruction.oneOutput
    let r0 : Result Reply := .ok (.Ok (),zero)
    let r1 : Result Reply := .ok (.Ok (),one)
    run nonce 16#usize 2 0#usize ⟨r0::r1::rest,reads⟩ =
      ⟨.returned (.ok (.Ok ⟨nonce,Array.repeat 32#usize 1#u8,Array.repeat 32#usize 1#u8⟩)),
        ⟨rest,reads ++ [(zero,r0),(zero,r1)]⟩⟩ := by
  letI : ExternalFuns := install ops
  dsimp only
  simp only [run,step,request ops nonce 16#usize 0#usize (by decide),resumeResult,
    bind_tc_ok,after_zero,finish,advance,add_zero_one,
    request ops nonce 16#usize 1#usize (by decide),after_one,List.append_assoc]
  rfl

#print axioms constant_after
#print axioms after_zero
#print axioms after_one
#print axioms add_zero_one
#print axioms zero_then_one
end R1Z.ProverRwEffectRegression
