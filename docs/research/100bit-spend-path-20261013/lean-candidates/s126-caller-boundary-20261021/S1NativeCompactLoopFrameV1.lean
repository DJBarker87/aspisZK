import S1NativeCompactBodyFrameV1
set_option autoImplicit false
namespace AspisS1NativeCompactBodyFrame
open Aeneas Aeneas.Std Result
open AspisS1NativeCompact

/-- Compose the exact source steps through the actual Std.loop. Both codec
Ok and Err returns preserve the prefix preceding the initial destination;
no correctness, totality or successful independent call of expandValues is
assumed. Failure/divergence remain allowed by the accepted-only statement. -/
theorem loop_frame (ops : Ops) (input out : Slice U8)
    (iter : core.ops.range.Range U8) (src dst : Usize) (n : Nat)
    (before : n≤dst.val) (r : Exit)
    (call : compact.expand_semantic_loop ops iter input out src dst=ok r) :
    Prefix n out r.2 := by
  change loop (fun (it,buf,s,d) => compact.expand_semantic_loop.body ops input it buf s d)
    (iter,out,src,dst)=ok r at call
  apply AspisS1LoopSafety.accepted
    (fun (it,buf,s,d) => compact.expand_semantic_loop.body ops input it buf s d)
    (fun (state : State) => n≤state.2.2.2.val ∧ Prefix n out state.2.1)
    (fun (exit : Exit) => Prefix n out exit.2) _ (iter,out,src,dst)
    ⟨before,fun _ _ => rfl⟩ r call
  intro state invariant result stepCall
  rcases state with ⟨it,buf,s,d⟩
  rcases invariant with ⟨destination,earlier⟩
  have frame := body_frame ops input buf it s d n destination result stepCall
  cases result with
  | cont state =>
    rcases state with ⟨it1,buf1,s1,d1⟩
    rcases frame with ⟨bound,kept⟩
    exact ⟨bound,fun j hj => (kept j hj).trans (earlier j hj)⟩
  | done exit =>
    rcases exit with ⟨status,buf1⟩
    exact fun j hj => (frame j hj).trans (earlier j hj)

#print axioms loop_frame
end AspisS1NativeCompactBodyFrame
