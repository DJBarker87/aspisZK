import Stage2ContinuationQueryLoop
import S4TenQueryFieldResultsRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1S4Stage2QueryCallRefinementV1
open AspisR1Stage2

private theorem adapted_ok_inv {A B E : Type}
    (call : Stage2ContinuationOwnedLoop.Call A B E) (a a1 : A) (b b1 : B)
    (h : Stage2ContinuationOwnedLoop.adapt call a b = .ok (.Ok (),a1,b1)) :
    call a b = .ok (.Ok (a1,b1)) := by
  unfold Stage2ContinuationOwnedLoop.adapt at h
  cases hc : call a b with
  | fail e => simp [hc] at h
  | div => simp [hc] at h
  | ok r =>
    cases r with
    | Err e => simp [hc] at h
    | Ok pair =>
      rcases pair with ⟨a2,b2⟩
      have hp : a2=a1 ∧ b2=b1 := by simpa [hc] using h
      rcases hp with ⟨rfl,rfl⟩
      rfl

private theorem refine_chain {A B E : Type} (next : A → Nat)
    (f g : Stage2ContinuationOwnedLoop.Call A B E)
    (href : ∀ a b a1 b1, f a b = .ok (.Ok (a1,b1)) → g a b = .ok (.Ok (a1,b1)))
    (a out : A) (b bout : B) (n : Nat)
    (h : Stage2ContinuationLoop.Chain next (Stage2ContinuationOwnedLoop.adapt f) a b out bout n) :
    Stage2ContinuationLoop.Chain next (Stage2ContinuationOwnedLoop.adapt g) a b out bout n := by
  induction h with
  | done a b hEnd => exact .done a b hEnd
  | step active hcall tail ih =>
    apply Stage2ContinuationLoop.Chain.step active ?_ ih
    have hf := adapted_ok_inv f _ _ _ _ hcall
    have hg := href _ _ _ _ hf
    simp [Stage2ContinuationOwnedLoop.adapt, hg]

private theorem run_success_of_chain {A B E : Type} (next : A → Nat)
    (call : Stage2ContinuationOwnedLoop.Call A B E)
    (a out : A) (b bout : B) (n : Nat)
    (h : Stage2ContinuationLoop.Chain next (Stage2ContinuationOwnedLoop.adapt call) a b out bout n) :
    Stage2ContinuationOwnedLoop.run next call a b = .ok (.Ok (out,bout)) := by
  induction h with
  | done a b hEnd =>
    unfold Stage2ContinuationOwnedLoop.run
    rw [Aeneas.Std.loop.eq_def]
    simp [Stage2ContinuationOwnedLoop.body, hEnd]
  | @step a a1 out b b1 bout n active hcall tail ih =>
    have hcall' := adapted_ok_inv call a a1 b b1 hcall
    have hnot : ¬ 22 ≤ next a := by omega
    unfold Stage2ContinuationOwnedLoop.run at ih ⊢
    rw [Aeneas.Std.loop.eq_def]
    simp [Stage2ContinuationOwnedLoop.body, hnot, hcall', ih]

private theorem query_loop_ten_run_eq (call : QueryCall) (proof : Slice U8)
    (p : verifier.Prepared) (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (obs : Option (verifier.Phase → Result Unit)) (geometry : verifier.QueryGeometry)
    (a : verifier.Accumulator) (b : verifier.BatchedWeights) :
    verifier.candidate.query_loop call proof p a g obs geometry b 10#usize =
      Stage2ContinuationOwnedLoop.run (fun x : verifier.Accumulator => x.next.val+12)
        (fun x y => call proof p x g obs geometry y) a b := by
  have hbody : verifier.candidate.query_loop_loop.body call proof p g obs geometry 10#usize =
      Stage2ContinuationOwnedLoop.body (fun x : verifier.Accumulator => x.next.val+12)
        (fun x y => call proof p x g obs geometry y) := by
    funext state
    cases state with
    | Err e => rfl
    | Ok pair =>
      rcases pair with ⟨x,y⟩
      change (if 10 ≤ x.next.val then _ else _) = (if 22 ≤ x.next.val+12 then _ else _)
      by_cases hx : 10 ≤ x.next.val
      · have hy : 22 ≤ x.next.val+12 := by omega
        simp only [if_pos hx, if_pos hy]
      · have hy : ¬22 ≤ x.next.val+12 := by omega
        simp only [if_neg hx, if_neg hy]
  unfold verifier.candidate.query_loop verifier.candidate.query_loop_loop
  simp only [hbody, Stage2ContinuationOwnedLoop.run]

theorem query_loop_ten_success_refines
    (f g : QueryCall) (proof : Slice U8) (p : verifier.Prepared)
    (values : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (obs : Option (verifier.Phase → Result Unit)) (geometry : verifier.QueryGeometry)
    (a out : verifier.Accumulator) (b bout : verifier.BatchedWeights)
    (hadvance : ∀ a a1 b b1, f proof p a values obs geometry b = .ok (.Ok (a1,b1)) →
      a1.next.val = a.next.val+1)
    (href : ∀ a b a1 b1, f proof p a values obs geometry b = .ok (.Ok (a1,b1)) →
      g proof p a values obs geometry b = .ok (.Ok (a1,b1)))
    (hstart : a.next.val=0)
    (hf : verifier.candidate.query_loop f proof p a values obs geometry b 10#usize =
      .ok (.Ok (out,bout))) :
    verifier.candidate.query_loop g proof p a values obs geometry b 10#usize =
      .ok (.Ok (out,bout)) := by
  have chainF := AspisR1S4TenQueryFieldResultsRootV1.emitted_ten_ordered_calls
    f proof p values obs geometry hadvance a out b bout hstart hf
  let callF : Stage2ContinuationOwnedLoop.Call verifier.Accumulator verifier.BatchedWeights verifier.Error :=
    fun x y => f proof p x values obs geometry y
  let callG : Stage2ContinuationOwnedLoop.Call verifier.Accumulator verifier.BatchedWeights verifier.Error :=
    fun x y => g proof p x values obs geometry y
  have chainG := refine_chain (fun x : verifier.Accumulator => x.next.val+12)
    callF callG (by intro x y x1 y1 hx; exact href x y x1 y1 hx)
    a out b bout 10 chainF
  have hrun := run_success_of_chain (fun x : verifier.Accumulator => x.next.val+12)
    callG a out b bout 10 chainG
  rw [query_loop_ten_run_eq g proof p values obs geometry a b]
  exact hrun

private theorem query_loop_twenty_two_run_eq (call : QueryCall) (proof : Slice U8)
    (p : verifier.Prepared) (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (obs : Option (verifier.Phase → Result Unit)) (geometry : verifier.QueryGeometry)
    (a : verifier.Accumulator) (b : verifier.BatchedWeights) :
    verifier.candidate.query_loop call proof p a g obs geometry b 22#usize =
      Stage2ContinuationOwnedLoop.run (fun x : verifier.Accumulator => x.next.val)
        (fun x y => call proof p x g obs geometry y) a b := by
  have hbody : verifier.candidate.query_loop_loop.body call proof p g obs geometry 22#usize =
      Stage2ContinuationOwnedLoop.body (fun x : verifier.Accumulator => x.next.val)
        (fun x y => call proof p x g obs geometry y) := by
    funext state
    cases state with
    | Err e => rfl
    | Ok pair => rcases pair with ⟨x,y⟩; rfl
  unfold verifier.candidate.query_loop verifier.candidate.query_loop_loop
  simp only [hbody, Stage2ContinuationOwnedLoop.run]

theorem query_loop_twelve_success_refines
    (f g : QueryCall) (proof : Slice U8) (p : verifier.Prepared)
    (values : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (obs : Option (verifier.Phase → Result Unit)) (geometry : verifier.QueryGeometry)
    (a out : verifier.Accumulator) (b bout : verifier.BatchedWeights)
    (hadvance : ∀ a a1 b b1, f proof p a values obs geometry b = .ok (.Ok (a1,b1)) →
      a1.next.val = a.next.val+1)
    (href : ∀ a b a1 b1, f proof p a values obs geometry b = .ok (.Ok (a1,b1)) →
      g proof p a values obs geometry b = .ok (.Ok (a1,b1)))
    (hstart : a.next.val=10)
    (hf : verifier.candidate.query_loop f proof p a values obs geometry b 22#usize =
      .ok (.Ok (out,bout))) :
    verifier.candidate.query_loop g proof p a values obs geometry b 22#usize =
      .ok (.Ok (out,bout)) := by
  have chainF := AspisR1Stage2.emitted_twelve_ordered_calls
    f proof p values obs geometry hadvance a out b bout hstart hf
  let callF : Stage2ContinuationOwnedLoop.Call verifier.Accumulator verifier.BatchedWeights verifier.Error :=
    fun x y => f proof p x values obs geometry y
  let callG : Stage2ContinuationOwnedLoop.Call verifier.Accumulator verifier.BatchedWeights verifier.Error :=
    fun x y => g proof p x values obs geometry y
  have chainG := refine_chain (fun x : verifier.Accumulator => x.next.val)
    callF callG (by intro x y x1 y1 hx; exact href x y x1 y1 hx)
    a out b bout 12 chainF
  have hrun := run_success_of_chain (fun x : verifier.Accumulator => x.next.val)
    callG a out b bout 12 chainG
  rw [query_loop_twenty_two_run_eq g proof p values obs geometry a b]
  exact hrun

#print axioms query_loop_ten_success_refines
#print axioms query_loop_twelve_success_refines
end AspisR1S4Stage2QueryCallRefinementV1
