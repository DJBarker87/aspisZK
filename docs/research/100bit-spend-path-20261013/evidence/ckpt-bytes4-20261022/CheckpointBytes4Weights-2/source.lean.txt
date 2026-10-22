import CheckpointBytes4Sections

set_option autoImplicit false
noncomputable section
namespace AspisR1.CheckpointBytes4Weights
open Aeneas Aeneas.Std Result
open AspisR1Stage2 CheckpointBytes4Sections

/-- Exact writeback at the next live slot, with every other element retained. -/
theorem replace_slot (pre old suffix : List K) (y x : K)
    (bound : (pre ++ y::old ++ suffix).length ≤ Usize.max) :
    Slice.setAtNat (⟨pre ++ y::old ++ suffix,bound⟩ : Slice K) pre.length x =
      ⟨(pre ++ [x]) ++ old ++ suffix,by simpa [List.length_append] using bound⟩ := by
  apply Subtype.ext
  simp [Slice.setAtNat,List.set_append_right]

/-- A successful sequential decode writes every field in order through the
actual mutable iterator. Prefix/suffix are arbitrary and retained. -/
theorem loop_success (read : ReadK) (old pre suffix xs : List K)
    (r last : verifier.Reader)
    (bound : (pre ++ old ++ suffix).length ≤ Usize.max)
    (success : readList read old.length r = ok (.Ok (xs,last))) :
    ∃ out : core.slice.iter.IterMut K,
      weightLoop read old.length r ⟨⟨pre ++ old ++ suffix,bound⟩,pre.length⟩ =
        ok (.Ok (out,last)) ∧
      out.slice.val = pre ++ xs ++ suffix ∧ out.i = pre.length + old.length := by
  induction old generalizing pre xs r with
  | nil =>
    have eq := core.result.Result.Ok.inj (Result.ok.inj success)
    have hx := congrArg Prod.fst eq
    have hr := congrArg Prod.snd eq
    dsimp only at hx hr
    subst xs last
    exact ⟨_,rfl,rfl,by simp⟩
  | cons y old ih =>
    simp only [List.length_cons,readList] at success
    obtain ⟨⟨value,next⟩,readRun,tail⟩ := OraclePortCkptAbiTry.bind_success _ _ _ success
    cases value with
    | Err e => cases tail
    | Ok x =>
      obtain ⟨rest,restRun,tail⟩ := OraclePortCkptAbiTry.bind_success _ _ _ tail
      cases rest with
      | Err e => cases tail
      | Ok pair =>
        rcases pair with ⟨ys,finish⟩
        have eq := core.result.Result.Ok.inj (Result.ok.inj tail)
        have hx := congrArg Prod.fst eq
        have hr := congrArg Prod.snd eq
        dsimp only at hx hr
        subst xs last
        have newBound : ((pre ++ [x]) ++ old ++ suffix).length ≤ Usize.max := by
          simpa [List.length_append] using bound
        obtain ⟨out,run,contents,cursor⟩ := ih (pre ++ [x]) ys next newBound restRun
        refine ⟨out,?_,?_,?_⟩
        · have slot : pre.length < (pre ++ y::old ++ suffix).length := by
            simp only [List.length_append,List.length_cons]; omega
          simp only [List.length_cons,weightLoop,core.slice.iter.IteratorIterMut.next]
          rw [dif_pos (show pre.length < (Slice.len ⟨pre ++ y::old ++ suffix,bound⟩).val from slot)]
          simp only [bind_tc_ok]
          rw [readRun]
          simp only [bind_tc_ok]
          change weightLoop read old.length next
            ⟨Slice.setAtNat (⟨pre ++ y::old ++ suffix,bound⟩ : Slice K) pre.length x,
              pre.length+1⟩ = _
          rw [replace_slot]
          simpa only [List.length_append,List.length_singleton] using run
        · simpa only [List.append_assoc,List.singleton_append] using contents
        · simpa only [List.length_append,List.length_singleton,List.length_cons,
            List.length_nil,Nat.zero_add,Nat.add_assoc,Nat.add_comm 1] using cursor

#print axioms replace_slot
#print axioms loop_success
end AspisR1.CheckpointBytes4Weights
end
