import S1OwnedQuerySourceBodyV1
set_option autoImplicit false
namespace AspisS1OwnedQueryBlock.Meaning
open Aeneas Aeneas.Std Result ControlFlow
open Query31ExplicitScanBody Query31ExplicitListLoop

def sourceAfter (xs : List U32) (out : AspisS1OwnedQueryBlock.Total.Output) :
    Result (ControlFlow (List U32 × Query31ExplicitScanBody.CurrentScan) (Query31ExplicitScanBody.CurrentScan × Option Bool)) :=
  let s : Query31ExplicitScanBody.CurrentScan := ⟨out.1,out.2.1,out.2.2.1⟩
  if out.2.2.2 then ok (.done (s,none)) else ok (.cont (xs,s))

/-- Full emitted-body equality for an arbitrary remaining iterator suffix.
The concrete prefix/membership operations are preserved and discharged. -/
theorem body_cons_owned (s : Query31ExplicitScanBody.CurrentScan) (x : U32) (xs : List U32)
    (hlen : s.accepted_len.val≤22) :
    body (stdOps listNext) (x::xs) s=(do
      let out ← owned_step s.accepted s.accepted_len s.draws x
      sourceAfter xs out) := by
  rw [owned_step_eq_stdWord _ _ _ _ hlen]
  by_cases full : s.accepted_len=22#usize
  · simp only [body,stdOps,listNext,stdWord,bind_tc_ok,if_pos full,sourceAfter,if_true]
    rfl
  by_cases exhausted : s.draws=64#usize
  · simp only [body,stdOps,listNext,stdWord,bind_tc_ok,if_neg full,if_pos exhausted,sourceAfter,if_true]
    rfl
  simp only [body,stdOps,listNext,stdWord,bind_tc_ok,if_neg full,if_neg exhausted,bind_assoc_eq]
  apply bind_congr
  intro d
  apply bind_congr
  intro sl
  apply bind_congr
  intro found
  cases found with
  | true => rfl
  | false =>
    simp only [Bool.false_eq_true,if_false,bind_assoc_eq]
    apply bind_congr
    intro a
    apply bind_congr
    intro n
    rfl

/-- One full source loop step composed with the concrete owned word; all
fail/div branches remain, and no child success is assumed. -/
theorem list_cons_owned (s : Query31ExplicitScanBody.CurrentScan) (x : U32) (xs : List U32)
    (hlen : s.accepted_len.val≤22) :
    scanListLoop (x::xs) s=(do
      let out ← owned_step s.accepted s.accepted_len s.draws x
      let sf : Query31ExplicitScanBody.CurrentScan := ⟨out.1,out.2.1,out.2.2.1⟩
      if out.2.2.2 then ok (sf,none) else scanListLoop xs sf) := by
  have unroll : scanListLoop (x::xs) s=(do
      let cf ← body (stdOps listNext) (x::xs) s
      match cf with
      | .done out => ok out
      | .cont (ys,sf) => scanListLoop ys sf) := by
    unfold scanListLoop step
    rw [loop.eq_def]
    cases h : body (stdOps listNext) (x::xs) s with
    | fail e => rfl
    | div => rfl
    | ok cf => cases cf with
      | done out => rfl
      | cont pair => cases pair;rfl
  rw [unroll,body_cons_owned s x xs hlen,bind_assoc_eq]
  apply bind_congr
  intro out
  rcases out with ⟨a,n,d,stop⟩
  cases stop <;> rfl

#print axioms body_cons_owned
#print axioms list_cons_owned
end AspisS1OwnedQueryBlock.Meaning
