import R13SourceTerminal
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1Stage2.R13Close

theorem bind_success {A B : Type} {m : Result A} {k : A → Result B} {v : B}
    (h : (do let x ← m; k x) = ok v) : ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- Partial correctness for the actual Aeneas least fixed point. No
termination, source simulation, or successful body call is assumed. -/
theorem loop_invariant {S T : Type} (body : S → Result (ControlFlow S T))
    (inv : S → Prop) (post : T → Prop)
    (step : ∀ s, inv s → ∀ r, body s = ok r →
      match r with | cont s' => inv s' | done out => post out)
    {s : S} {out : T} (hi : inv s) (h : loop body s = ok out) : post out := by
  have aux : ∀ s, loop body s = div ∨
      ∀ out, inv s → loop body s = ok out → post out := by
    apply loop.fixpoint_induct body
      (motive := fun f => ∀ s, f s = div ∨ ∀ out, inv s → f s = ok out → post out)
    · apply Lean.Order.admissible_pi_apply
        (fun s (r : Result T) => r = div ∨ ∀ out, inv s → r = ok out → post out)
      intro s
      exact Lean.Order.admissible_flatOrder _ (Or.inl rfl)
    · intro f ih s
      dsimp only
      cases hb : body s with
      | fail e => right; intro out _ he; simp only [hb] at he; cases he
      | div => exact Or.inl (by simp only [hb])
      | ok r =>
        cases r with
        | done value =>
          right
          intro out hs he
          simp only [hb] at he
          cases he
          exact step s hs (.done value) hb
        | cont s' =>
          rcases ih s' with hd | hp
          · exact Or.inl (by simpa only [hb] using hd)
          · right
            intro out hs he
            exact hp out (step s hs (.cont s') hb) (by simpa only [hb] using he)
  rcases aux s with hd | hp
  · rw [hd] at h; cases h
  · exact hp out hi h

/-- Exact successful mutable write, including its bounds. -/
theorem update_success {A : Type} {n : Usize} (a b : Array A n)
    (i : Usize) (x : A) (h : Array.update a i x = ok b) :
    i.val < a.val.length ∧ b.val = a.val.set i.val x := by
  unfold Array.update at h
  split at h
  · cases h
  · rename_i old he
    have hb : i.val < a.val.length := by
      have hh : a.val[i.val]? = some old := he
      exact List.getElem?_eq_some_iff.mp hh |>.1
    exact ⟨hb, congrArg (fun v : Array A n => v.val) (Result.ok.inj h).symm⟩

/-- A write before the unread cursor cannot change an unread cell. -/
theorem update_unread {A : Type} {n : Usize} (a b : Array A n)
    (w : Usize) (x : A) (cursor j : Nat) (hw : w.val < cursor)
    (hj : cursor ≤ j) (h : Array.update a w x = ok b) :
    b.val[j]? = a.val[j]? := by
  obtain ⟨_, hb⟩ := update_success a b w x h
  rw [hb, List.getElem?_set]
  simp [show w.val ≠ j by omega]

#print axioms bind_success
#print axioms loop_invariant
#print axioms update_success
#print axioms update_unread
end AspisR1Stage2.R13Close
