import Port4B_TreeCuts

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4B_AnyFalse
open Aeneas Aeneas.Std Result ControlFlow

theorem body_nil (predicate : core.ops.function.FnMut Unit (Slice U8) Bool) (remainder : Slice U8) :
    Port3_BatchStd.anyBody (core.iter.traits.iterator.IteratorChunksExact U8) predicate
      ({chunks:=[],remainder:=remainder},()) = ok (.done (false,{chunks:=[],remainder:=remainder})) := rfl

theorem body_cons (predicate : core.ops.function.FnMut Unit (Slice U8) Bool)
    (chunk : Slice U8) (rest : List (Slice U8)) (remainder : Slice U8) :
    Port3_BatchStd.anyBody (core.iter.traits.iterator.IteratorChunksExact U8) predicate
      ({chunks:=chunk::rest,remainder:=remainder},()) =
      (do let (stop,state) ← predicate.call_mut () chunk
          if stop then ok (.done (true,{chunks:=rest,remainder:=remainder}))
          else ok (.cont ({chunks:=rest,remainder:=remainder},state))) := rfl

/-- An accepted false native any-scan calls EVERY physical chunk in order;
no total predicate contract or rejected-run equivalence is required. -/
theorem all_chunks (predicate : core.ops.function.FnMut Unit (Slice U8) Bool)
    (chunks : List (Slice U8)) (remainder : Slice U8)
    (after : core.slice.iter.ChunksExact U8)
    (returned : Port3_BatchStd.anyDefault (core.iter.traits.iterator.IteratorChunksExact U8)
      predicate {chunks:=chunks,remainder:=remainder} () = ok (false,after)) :
    (∀ chunk∈chunks, predicate.call_mut () chunk=ok (false,())) ∧ after.chunks=[] := by
  induction chunks with
  | nil =>
    unfold Port3_BatchStd.anyDefault at returned
    rw [Aeneas.Std.loop.eq_def] at returned
    rw [body_nil] at returned
    have eq := Result.ok.inj returned
    cases eq
    exact ⟨by simp,rfl⟩
  | cons chunk rest ih =>
    unfold Port3_BatchStd.anyDefault at returned
    rw [Aeneas.Std.loop.eq_def] at returned
    rw [body_cons] at returned
    generalize call : predicate.call_mut () chunk=r at returned
    cases r with
    | fail e => cases returned
    | div => cases returned
    | ok pair =>
      rcases pair with ⟨stop,state⟩
      cases state
      simp only [bind_tc_ok] at returned
      cases stop with
      | true => cases returned
      | false =>
        change Port3_BatchStd.anyDefault (core.iter.traits.iterator.IteratorChunksExact U8)
          predicate {chunks:=rest,remainder:=remainder} ()=ok (false,after) at returned
        have tail := ih returned
        exact ⟨by intro c mem;rcases List.mem_cons.mp mem with rfl|h;exact call;exact tail.1 c h,tail.2⟩

#print axioms body_nil
#print axioms body_cons
#print axioms all_chunks
end AspisR1.Port4B_AnyFalse
end
