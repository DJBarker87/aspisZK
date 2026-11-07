/-
AMN_ReturnedPath: generic returned-path inversion lemmas for the RSL reference
monad.  Target not yet established.  Core Lean plus RSL_Base only.

Purpose.  The minimal A1/A2 obligations (AMN_Minimal) only ever start from a
RETURNED observation of an RSL reference (`o.exit = .ret r`).  Along such an
observation every allocation site took its success branch and no panic was
reached, so the reference behaves like a straight-line function.  These lemmas
let a worker walk a row's reference along its returned path one combinator at
a time (bind / seq / check / ofOption / ofExcept / ofCloned / index / lift /
call) and read off the child results that the model must reproduce.  They are
the one-time tool that replaces NND's both-arm, exact-payload case analysis.

No sorry, no axiom.
-/
import RSL_Base
set_option autoImplicit false

namespace RSL.AMN

/-! ## Spec layer -/

theorem Spec.bind_ret {α β : Type} {m : Spec α} {k : α → Spec β} {env : Env} {o : Obs β}
    {x : β} (h : Spec.bind m k env o) (hx : o.exit = .ret x) :
    ∃ a e1 o2, m env ⟨.ret a, e1⟩ ∧ k a env o2 ∧ o2.exit = .ret x := by
  rcases h with ⟨a, e1, o2, h1, h2, ho⟩ | ⟨e1, _, ho⟩ | ⟨e1, _, ho⟩
  · subst ho
    exact ⟨a, e1, o2, h1, h2, hx⟩
  · subst ho; cases hx
  · subst ho; cases hx

theorem Spec.call_ret {A B : Type} {dom : A → Prop} {law : A → Spec B} {a : A} {env : Env}
    {o : Obs B} (h : Spec.call dom law a env o) : dom a ∧ law a env o := h

theorem Spec.pure_ret {α : Type} {a x : α} {env : Env} {o : Obs α}
    (h : Spec.pure a env o) (hx : o.exit = .ret x) : x = a := by
  unfold Spec.pure at h
  subst h
  cases hx
  rfl

/-- A panic admits no returned observation. -/
theorem Spec.panic_no_ret {α : Type} {env : Env} {o : Obs α} {x : α}
    (h : (Spec.panic : Spec α) env o) (hx : o.exit = .ret x) : False := by
  unfold Spec.panic at h
  subst h
  cases hx

/-! ## Result layer -/

theorem RS.bind_ret_ok {α β : Type} {m : RS α} {k : α → RS β} {env : Env}
    {o : Obs (Except ProgramError β)} {x : β}
    (h : RS.bind m k env o) (hx : o.exit = .ret (.ok x)) :
    ∃ a e1 o2, m env ⟨.ret (.ok a), e1⟩ ∧ k a env o2 ∧ o2.exit = .ret (.ok x) := by
  obtain ⟨r, e1, o2, h1, h2, h3⟩ := Spec.bind_ret h hx
  cases r with
  | ok a => exact ⟨a, e1, o2, h1, h2, h3⟩
  | error e =>
    have := Spec.pure_ret h2 h3
    cases this

theorem RS.bind_ret_error {α β : Type} {m : RS α} {k : α → RS β} {env : Env}
    {o : Obs (Except ProgramError β)} {e : ProgramError}
    (h : RS.bind m k env o) (hx : o.exit = .ret (.error e)) :
    (∃ e1, m env ⟨.ret (.error e), e1⟩) ∨
      (∃ a e1 o2, m env ⟨.ret (.ok a), e1⟩ ∧ k a env o2 ∧ o2.exit = .ret (.error e)) := by
  obtain ⟨r, e1, o2, h1, h2, h3⟩ := Spec.bind_ret h hx
  cases r with
  | ok a => exact Or.inr ⟨a, e1, o2, h1, h2, h3⟩
  | error e' =>
    have := Spec.pure_ret h2 h3
    cases this
    exact Or.inl ⟨e1, h1⟩

theorem RS.seq_ret_ok {β : Type} {m : RS Unit} {k : RS β} {env : Env}
    {o : Obs (Except ProgramError β)} {x : β}
    (h : RS.seq m k env o) (hx : o.exit = .ret (.ok x)) :
    ∃ e1 o2, m env ⟨.ret (.ok ()), e1⟩ ∧ k env o2 ∧ o2.exit = .ret (.ok x) := by
  obtain ⟨u, e1, o2, h1, h2, h3⟩ := RS.bind_ret_ok h hx
  cases u
  exact ⟨e1, o2, h1, h2, h3⟩

theorem RS.check_ret_ok {bad : Bool} {e : ProgramError} {env : Env}
    {o : Obs (Except ProgramError Unit)} {x : Unit}
    (h : RS.check bad e env o) (hx : o.exit = .ret (.ok x)) : bad = false := by
  cases bad with
  | false => rfl
  | true =>
    change Spec.pure (Except.error e) env o at h
    have := Spec.pure_ret h hx
    cases this

theorem RS.ofOption_ret_ok {α : Type} {x : Option α} {e : ProgramError} {env : Env}
    {o : Obs (Except ProgramError α)} {a : α}
    (h : RS.ofOption x e env o) (hx : o.exit = .ret (.ok a)) : x = some a := by
  cases x with
  | none =>
    change Spec.pure (Except.error e) env o at h
    have := Spec.pure_ret h hx
    cases this
  | some b =>
    change Spec.pure (Except.ok b) env o at h
    have := Spec.pure_ret h hx
    cases this
    rfl

theorem RS.ofExcept_ret {α : Type} {x : Except ProgramError α} {env : Env}
    {o : Obs (Except ProgramError α)} {r : Except ProgramError α}
    (h : RS.ofExcept x env o) (hx : o.exit = .ret r) : r = x :=
  Spec.pure_ret h hx

theorem RS.ofCloned_ret_ok {α : Type} {x : Except ProgramError α} {env : Env}
    {o : Obs (Except ProgramError α)} {a : α}
    (h : RS.ofCloned x env o) (hx : o.exit = .ret (.ok a)) : x = .ok a := by
  cases x with
  | ok b =>
    change Spec.pure (Except.ok b) env o at h
    have := Spec.pure_ret h hx
    cases this
    rfl
  | error e =>
    cases hc : e.cloneAllocates with
    | true =>
      simp only [RS.ofCloned, hc, if_true] at h
      obtain ⟨_, _, o2, _, h2, h3⟩ := RS.bind_ret_ok h hx
      change Spec.pure (Except.error e) env o2 at h2
      have := Spec.pure_ret h2 h3
      cases this
    | false =>
      simp only [RS.ofCloned, hc, Bool.false_eq_true, if_false] at h
      change Spec.pure (Except.error e) env o at h
      have := Spec.pure_ret h hx
      cases this

theorem RS.index_ret_ok {α : Type} {l : List α} {i : Nat} {env : Env}
    {o : Obs (Except ProgramError α)} {a : α}
    (h : RS.index l i env o) (hx : o.exit = .ret (.ok a)) : l[i]? = some a := by
  cases hl : l[i]? with
  | some b =>
    simp only [RS.index, hl] at h
    change Spec.pure (Except.ok b) env o at h
    have := Spec.pure_ret h hx
    cases this
    rfl
  | none =>
    exfalso
    simp only [RS.index, hl] at h
    unfold RS.lift Spec.map at h
    obtain ⟨_, _, _, h1, _, _⟩ := Spec.bind_ret h hx
    exact Spec.panic_no_ret h1 rfl

theorem RS.lift_ret_ok {α : Type} {m : Spec α} {env : Env}
    {o : Obs (Except ProgramError α)} {x : α}
    (h : RS.lift m env o) (hx : o.exit = .ret (.ok x)) : ∃ e1, m env ⟨.ret x, e1⟩ := by
  unfold RS.lift Spec.map at h
  obtain ⟨a, e1, o2, h1, h2, h3⟩ := Spec.bind_ret h hx
  have := Spec.pure_ret h2 h3
  cases this
  exact ⟨e1, h1⟩

/-- An infallible lifted Spec never returns a Rust `Err`. -/
theorem RS.lift_no_error {α : Type} {m : Spec α} {env : Env}
    {o : Obs (Except ProgramError α)} {e : ProgramError}
    (h : RS.lift m env o) (hx : o.exit = .ret (.error e)) : False := by
  unfold RS.lift Spec.map at h
  obtain ⟨a, _, o2, _, h2, h3⟩ := Spec.bind_ret h hx
  have := Spec.pure_ret h2 h3
  cases this

/-! ## Teeth: why membership alone does not give liveness

An allocation site admits both the returned and the aborting observation at
the SAME environment.  Hence "the model's lifted observation lies in the
reference" (a model-side RowSpec) does not imply that the model returns where
the reference can return; a route through model-side RowSpecs must prove that
liveness separately (AMN_Minimal.viaModelSpec). -/
theorem alloc_admits_both (env : Env) :
    RS.lift Spec.alloc env ⟨.ret (.ok ()), []⟩ ∧ RS.lift Spec.alloc env ⟨.abort, []⟩ :=
  ⟨(RS.lift_alloc_iff env _).mpr (Or.inl rfl), (RS.lift_alloc_iff env _).mpr (Or.inr rfl)⟩

#print axioms Spec.bind_ret
#print axioms RS.bind_ret_ok
#print axioms RS.bind_ret_error
#print axioms RS.seq_ret_ok
#print axioms RS.check_ret_ok
#print axioms RS.ofOption_ret_ok
#print axioms RS.ofExcept_ret
#print axioms RS.ofCloned_ret_ok
#print axioms RS.index_ret_ok
#print axioms RS.lift_ret_ok
#print axioms RS.lift_no_error
#print axioms alloc_admits_both

end RSL.AMN
