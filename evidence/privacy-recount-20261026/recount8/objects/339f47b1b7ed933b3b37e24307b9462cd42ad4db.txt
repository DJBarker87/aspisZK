import R1Z.ProverRwEffectTape

/-! Source-specific error and cap laws for the factored entropy owner. -/
set_option autoImplicit false
namespace R1Z.ProverRwEffectControl
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open ProverRwEffectSource ProverRwEffectTape
variable [ExternalTypes] [ExternalFuns]

theorem after_os_error (nonce : Array U8 32#usize) (retry : Usize)
    (back : Back) (err : getrandom.error.Error) (bytes : Slice U8) :
    after nonce retry back (.Err err,bytes) = .ok (.done (.Err (.Os err))) := by
  rfl

theorem at_limit (nonce : Array U8 32#usize) (limit retry : Usize)
    (h : ¬ retry < limit) (world : World) :
    step nonce limit retry world =
      ⟨.returned (.ok (.Err .RepeatedZeroBlock)),world⟩ := by
  simp only [step,emit,h,if_false,finish]

/-- A served read is retained even when the external itself fails. -/
theorem failed_read (nonce : Array U8 32#usize) (limit retry : Usize)
    (input : Slice U8) (resume : Reply → Result Outcome)
    (h : emit nonce limit retry = .read input resume) (err : Aeneas.Std.Error)
    (rest : List (Result Reply)) (reads : List (Slice U8 × Result Reply)) :
    step nonce limit retry ⟨.fail err::rest,reads⟩ =
      ⟨.returned (.fail err),⟨rest,reads ++ [(input,.fail err)]⟩⟩ := by
  rw [step_served nonce limit retry input resume h]
  rfl

theorem diverged_read (nonce : Array U8 32#usize) (limit retry : Usize)
    (input : Slice U8) (resume : Reply → Result Outcome)
    (h : emit nonce limit retry = .read input resume)
    (rest : List (Result Reply)) (reads : List (Slice U8 × Result Reply)) :
    step nonce limit retry ⟨.div::rest,reads⟩ =
      ⟨.returned .div,⟨rest,reads ++ [(input,.div)]⟩⟩ := by
  rw [step_served nonce limit retry input resume h]
  rfl

/-- Under the exact prefix-call fact, an OS error stops the actual emitted
continuation and records the draw. No predicate about successful output is used. -/
theorem os_error_read (nonce : Array U8 32#usize) (limit retry : Usize)
    (below : retry < limit) (input : Slice U8) (back : Back)
    (hprefix : before = .ok (input,back)) (err : getrandom.error.Error)
    (bytes : Slice U8) (rest : List (Result Reply))
    (reads : List (Slice U8 × Result Reply)) :
    step nonce limit retry ⟨.ok (.Err err,bytes)::rest,reads⟩ =
      ⟨.returned (.ok (.Err (.Os err))),
        ⟨rest,reads ++ [(input,.ok (.Err err,bytes))]⟩⟩ := by
  have call : emit nonce limit retry = .read input (after nonce retry back) := by
    simp only [emit,below,if_true,hprefix]
  rw [step_served nonce limit retry input (after nonce retry back) call]
  simp only [resumeResult,bind_tc_ok,after_os_error,finish]

#print axioms after_os_error
#print axioms at_limit
#print axioms failed_read
#print axioms diverged_read
#print axioms os_error_read
end R1Z.ProverRwEffectControl
