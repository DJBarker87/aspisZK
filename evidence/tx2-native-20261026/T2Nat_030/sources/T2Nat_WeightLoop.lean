import T2Nat_WeightsCongr
set_option autoImplicit false
noncomputable section
namespace AspisR1.T2Nat_WeightLoop
open Aeneas Aeneas.Std Result AspisR1Stage2
open CheckpointBytes4Sections
abbrev K := aspis_core.field.QM31

def result (slice : Slice K) (start n : Nat)
    (value : core.result.Result (List K × verifier.Reader) verifier.Error) :
    Result (core.result.Result (core.slice.iter.IterMut K × verifier.Reader) verifier.Error) :=
  match value with
  | .Err e => ok (.Err e)
  | .Ok (xs,last) => ok (.Ok (⟨Port5Q2_ReaderWeights.write slice start xs,start+n⟩,last))

/-- Normalize the retained mutable iterator symbolically, preserving all
errors/failures and using the actual std next/writeback operations. -/
theorem normalize (read : ReadK) (old pre : List K) (r : verifier.Reader)
    (bound : (pre++old).length ≤ Usize.max) :
    weightLoop read old.length r ⟨⟨pre++old,bound⟩,pre.length⟩ =
      (do let value ← readList read old.length r
          result ⟨pre++old,bound⟩ pre.length old.length value) := by
  induction old generalizing pre r with
  | nil => simp only [List.length_nil,weightLoop,readList,bind_tc_ok,result,
      Port5Q2_ReaderWeights.write,Nat.add_zero]
  | cons y old ih =>
    have slot : pre.length < (pre++y::old).length := by
      simp only [List.length_append,List.length_cons]; omega
    simp only [List.length_cons,weightLoop,core.slice.iter.IteratorIterMut.next]
    rw [dif_pos (show pre.length < (Slice.len ⟨pre++y::old,bound⟩).val from slot)]
    simp only [bind_tc_ok,readList,bind_assoc_eq]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro pair called
    rcases pair with ⟨value,next⟩
    cases value with
    | Err e => rfl
    | Ok x =>
      change weightLoop read old.length next
        ⟨Slice.setAtNat (⟨pre++y::old,bound⟩ : Slice K) pre.length x,pre.length+1⟩ = _
      have replaced := CheckpointBytes4Weights.replace_slot pre old [] y x (by simpa using bound)
      simp only [List.append_nil] at replaced
      rw [replaced]
      have bound1 : ((pre++[x])++old).length ≤ Usize.max := by
        simp only [List.length_append,List.length_cons,List.length_nil] at bound ⊢
        omega
      have recursive := ih (pre++[x]) next bound1
      simp only [List.length_append,List.length_singleton] at recursive
      rw [recursive]
      simp only [Aeneas.Std.uncurry,bind_assoc_eq,bind_tc_ok]
      apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro rest tail
      cases rest with
      | Err e => rfl
      | Ok pair =>
        rcases pair with ⟨xs,last⟩
        have count := read_list_length read old.length next last xs tail
        have wholeCount : (x::xs).length = (y::old).length := by simp only [List.length_cons,count]
        have before := Port5Q2_ReaderWeights.write_shape pre (y::old) (x::xs) bound wholeCount
        have after := Port5Q2_ReaderWeights.write_shape (pre++[x]) old xs bound1 count
        simp only [result,bind_tc_ok,Aeneas.Std.uncurry]
        apply congrArg Result.ok
        apply congrArg core.result.Result.Ok
        apply Prod.ext
        · apply congrArg₂ (fun (s : Slice K) (i : Nat) => (⟨s,i⟩ : core.slice.iter.IterMut K))
          · apply Subtype.ext
            simpa only [List.length_append,List.length_singleton] using
              after.trans (by simpa only [List.append_assoc,List.singleton_append] using before.symm)
          · omega
        · rfl

#print axioms normalize
end AspisR1.T2Nat_WeightLoop
end
