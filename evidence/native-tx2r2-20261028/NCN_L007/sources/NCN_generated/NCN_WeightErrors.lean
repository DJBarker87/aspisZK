import CheckpointBytes4Weights
set_option autoImplicit false
noncomputable section
namespace AspisR1.NCN_WeightErrors
open Aeneas Aeneas.Std Result AspisR1Stage2
open CheckpointBytes4Sections

/-- A decoder error at any reached slot stops the actual mutable model loop.
There is no requested value or execution result in the lower hypotheses. -/
theorem loop_error (read : ReadK) (old pre suffix : List K)
    (r : verifier.Reader) (e : verifier.Error)
    (bound : (pre ++ old ++ suffix).length ≤ Usize.max)
    (failure : readList read old.length r = ok (.Err e)) :
    weightLoop read old.length r ⟨⟨pre ++ old ++ suffix,bound⟩,pre.length⟩ =
      ok (.Err e) := by
  induction old generalizing pre r with
  | nil => cases failure
  | cons y old ih =>
    simp only [List.length_cons,readList] at failure
    obtain ⟨⟨value,next⟩,readRun,tail⟩ := OraclePortCkptAbiTry.bind_success _ _ _ failure
    have slot : pre.length < (pre ++ y::old ++ suffix).length := by
      simp only [List.length_append,List.length_cons]; omega
    simp only [List.length_cons,weightLoop,core.slice.iter.IteratorIterMut.next]
    rw [dif_pos (show pre.length < (Slice.len ⟨pre ++ y::old ++ suffix,bound⟩).val from slot)]
    simp only [bind_tc_ok]
    rw [readRun]
    simp only [bind_tc_ok]
    cases value with
    | Err err =>
      change ok (core.result.Result.Err err) = ok (core.result.Result.Err e) at tail
      have he : err=e := core.result.Result.Err.inj (Result.ok.inj tail)
      subst err
      rfl
    | Ok x =>
      change (do
        let rest ← readList read old.length next
        match rest with
        | .Err e => ok (.Err e)
        | .Ok (xs,last) => ok (.Ok (x::xs,last)) : Result (core.result.Result (List K × verifier.Reader) verifier.Error)) = ok (.Err e) at tail
      obtain ⟨rest,restRun,tail⟩ := OraclePortCkptAbiTry.bind_success _ _ _ tail
      cases rest with
      | Ok pair => cases tail
      | Err err =>
        have he : err=e := core.result.Result.Err.inj (Result.ok.inj tail)
        subst err
        have newBound : ((pre ++ [x]) ++ old ++ suffix).length ≤ Usize.max := by
          simpa [List.length_append] using bound
        have h := ih (pre ++ [x]) next newBound restRun
        change weightLoop read old.length next
          ⟨Slice.setAtNat (⟨pre ++ y::old ++ suffix,bound⟩ : Slice K) pre.length x,
            pre.length+1⟩ = _
        rw [CheckpointBytes4Weights.replace_slot]
        simpa only [List.length_append,List.length_singleton] using h

#print axioms loop_error
end AspisR1.NCN_WeightErrors
