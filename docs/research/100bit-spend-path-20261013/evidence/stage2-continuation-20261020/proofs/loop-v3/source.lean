import Aeneas
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace Stage2ContinuationLoop
variable {A B E : Type}

abbrev Call (A B E : Type) := A → B → Result (core.result.Result Unit E × A × B)

def body (next : A → Nat) (call : Call A B E) (a : A) (b : B) :
    Result (ControlFlow (A × B) (A × B × Option (core.result.Result Unit E))) := do
  if next a < 22 then
    let (r, a1, b1) ← call a b
    match r with
    | .Ok _ => ok (cont (a1,b1))
    | .Err e => ok (done (a1,b1,some (.Err e)))
  else ok (done (a,b,none))

def run (next : A → Nat) (call : Call A B E) (a : A) (b : B) :=
  Aeneas.Std.loop (fun s : A × B => body next call s.1 s.2) (a,b)

inductive Chain (next : A → Nat) (call : Call A B E) : A → B → A → B → Nat → Prop
  | done (a : A) (b : B) (atEnd : next a = 22) : Chain next call a b a b 0
  | step {a a1 out : A} {b b1 bout : B} {n : Nat}
      (active : next a < 22)
      (callOk : call a b = ok (.Ok (),a1,b1))
      (tail : Chain next call a1 b1 out bout n) :
      Chain next call a b out bout (n+1)

private theorem loop_cases {S T : Type} (step : S → Result (ControlFlow S T))
    (s : S) (out : T) (h : Aeneas.Std.loop step s = ok out) :
    step s = ok (.done out) ∨
    ∃ s1, step s = ok (.cont s1) ∧ Aeneas.Std.loop step s1 = ok out := by
  rw [Aeneas.Std.loop.eq_def] at h
  cases hs : step s with
  | fail e => simp [hs] at h
  | div => simp [hs] at h
  | ok cf =>
    cases cf with
    | done value => simp [hs] at h; subst value; exact Or.inl rfl
    | cont s1 => simp [hs] at h; exact Or.inr ⟨s1,rfl,h⟩

private theorem body_done (next : A → Nat) (call : Call A B E)
    (a out : A) (b bout : B) (ha : next a ≤ 22)
    (h : body next call a b = ok (.done (out,bout,none))) :
    next a = 22 ∧ a = out ∧ b = bout := by
  unfold body at h
  split at h
  · cases hc : call a b with
    | fail e => simp [hc] at h
    | div => simp [hc] at h
    | ok triple =>
      rcases triple with ⟨r,a1,b1⟩
      cases r <;> simp [hc] at h
  · have hp : a = out ∧ b = bout := by simpa using h
    exact ⟨by omega, hp⟩

private theorem body_cont (next : A → Nat) (call : Call A B E)
    (a a1 : A) (b b1 : B)
    (h : body next call a b = ok (.cont (a1,b1))) :
    next a < 22 ∧ call a b = ok (.Ok (),a1,b1) := by
  unfold body at h
  split at h
  · rename_i active
    cases hc : call a b with
    | fail e => simp [hc] at h
    | div => simp [hc] at h
    | ok triple =>
      rcases triple with ⟨r,a2,b2⟩
      cases r with
      | Err e => simp [hc] at h
      | Ok payload =>
        cases payload
        have hp : a2 = a1 ∧ b2 = b1 := by simpa [hc] using h
        rcases hp with ⟨rfl,rfl⟩
        exact ⟨active,rfl⟩
  · cases h

theorem successful_loop_chain (next : A → Nat) (call : Call A B E)
    (advance : ∀ a a1 b b1, call a b = ok (.Ok (),a1,b1) → next a1 = next a + 1)
    (a out : A) (b bout : B) (ha : next a ≤ 22)
    (h : run next call a b = ok (out,bout,none)) :
    Chain next call a b out bout (22-next a) := by
  let step := fun s : A × B => body next call s.1 s.2
  have hl : Aeneas.Std.loop step (a,b) = ok (out,bout,none) := h
  clear h
  induction hfuel : 22-next a generalizing a b with
  | zero =>
    rcases loop_cases step (a,b) (out,bout,none) hl with hd | ⟨⟨a1,b1⟩,hc,ht⟩
    · obtain ⟨he,rfl,rfl⟩ := body_done next call a out b bout ha hd
      exact Chain.done a b he
    · have active := (body_cont next call a a1 b b1 hc).1
      omega
  | succ k ih =>
    rcases loop_cases step (a,b) (out,bout,none) hl with hd | ⟨⟨a1,b1⟩,hc,ht⟩
    · have he := (body_done next call a out b bout ha hd).1
      omega
    · obtain ⟨active,hcall⟩ := body_cont next call a a1 b b1 hc
      have hnext := advance a a1 b b1 hcall
      have hchain : Chain next call a1 b1 out bout k := by
        apply ih (a := a1) (b := b1)
        · omega
        · exact ht
        · omega
      exact Chain.step active hcall hchain

theorem twelve_ordered_calls (next : A → Nat) (call : Call A B E)
    (advance : ∀ a a1 b b1, call a b = ok (.Ok (),a1,b1) → next a1 = next a + 1)
    (a out : A) (b bout : B) (start : next a = 10)
    (h : run next call a b = ok (out,bout,none)) :
    Chain next call a b out bout 12 := by
  have hc := successful_loop_chain next call advance a out b bout (by omega) h
  simpa only [start] using hc

#print axioms loop_cases
#print axioms body_done
#print axioms body_cont
#print axioms successful_loop_chain
#print axioms twelve_ordered_calls
end Stage2ContinuationLoop
