import S1NativeCompactLengthsV1
set_option autoImplicit false
namespace AspisS1NativeCompactLengths
open Aeneas Aeneas.Std Result
open AspisS1NativeCompact AspisS1NativeCompactBodyFrame

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (m >>= k)=ok v) : ∃ x,m=ok x ∧ k x=ok v := by
  cases m with
  | ok x => exact ⟨x,rfl,h⟩
  | fail e => cases h
  | div => cases h
private theorem pair_success {α β γ : Type} (m : Result (α × β))
    (k : α → β → Result γ) (v : γ)
    (h : (do let (a,b) ← m; k a b)=ok v) :
    ∃ a b,m=ok (a,b) ∧ k a b=ok v := by
  cases m with
  | ok pair => cases pair with | mk a b => exact ⟨a,b,rfl,h⟩
  | fail e => cases h
  | div => cases h

/-- Every accepted loop return preserves the actual output-buffer length,
including codec Err. The value leaf can fail, diverge or return any buffer. -/
theorem loop_length (ops : Ops) (input out : Slice U8)
    (iter : core.ops.range.Range U8) (src dst : Usize) (r : Exit)
    (call : compact.expand_semantic_loop ops iter input out src dst=ok r) :
    r.2.length=out.length := by
  change loop (fun (it,buf,s,d) => compact.expand_semantic_loop.body ops input it buf s d)
    (iter,out,src,dst)=ok r at call
  apply AspisS1LoopSafety.accepted
    (fun (it,buf,s,d) => compact.expand_semantic_loop.body ops input it buf s d)
    (fun (state : State) => state.2.1.length=out.length)
    (fun (exit : Exit) => exit.2.length=out.length) _ (iter,out,src,dst) rfl r call
  intro state invariant result stepCall
  rcases state with ⟨it,buf,s,d⟩
  have frame := body_length ops input buf it s d result stepCall
  cases result with
  | cont state =>
    rcases state with ⟨it1,buf1,s1,d1⟩
    exact frame.trans invariant
  | done exit =>
    rcases exit with ⟨status,buf1⟩
    exact frame.trans invariant

/-- Full unchanged native expand_semantic preserves buffer length on every
outer accepted result, including all early codec errors. No totality or
independent successful child call is assumed. -/
theorem semantic_length (ops : Ops) (input out expanded : Slice U8)
    (status : core.result.Result Unit compact.CodecError)
    (success : compact.expand_semantic ops input out=ok (status,expanded)) :
    expanded.length=out.length := by
  unfold compact.expand_semantic at success
  obtain ⟨compactLength,hcompactLength,success⟩ := bind_success _ _ _ success
  split at success
  · have same := Result.ok.inj success
    exact congrArg (fun pair => (pair.2 : Slice U8).length) same.symm
  · obtain ⟨logicalLength,hlogicalLength,success⟩ := bind_success _ _ _ success
    split at success
    · have same := Result.ok.inj success
      exact congrArg (fun pair => (pair.2 : Slice U8).length) same.symm
    · obtain ⟨header,back,hheader,success⟩ := pair_success _ _ _ success
      obtain ⟨sourceHeader,hsourceHeader,success⟩ := bind_success _ _ _ success
      obtain ⟨replacement,hreplacement,success⟩ := bind_success _ _ _ success
      have initial := rangeTo_length out header back 32#usize hheader replacement
      have kept := loop_length ops input (back replacement)
        {start:=0#u8,«end»:=compact.SEMANTIC_ROWS} 32#usize 32#usize
        (status,expanded) success
      exact kept.trans initial

#print axioms loop_length
#print axioms semantic_length
end AspisS1NativeCompactLengths
