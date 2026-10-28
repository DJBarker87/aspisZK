import R1Z.PV_W_SourceSyntax
set_option autoImplicit false
namespace R1Z.PV_W_Loops
open PV_W_Threading Aeneas.Std
variable {W C E S A : Type}

def fuel (body : S → M W C E (ControlFlow S A)) : Nat → S → M W C E A
  | 0,_ => lift .div
  | n+1,s => PV_W_Threading.bind (body s) (fun cf => match cf with
      | .cont next => fuel body n next
      | .done a => lift (.ok a))

/-- Finite operational derivation. Each iteration keeps its exact world,
ordered trace, error payload, and nonreturning prefix. Infinite control flow
is not asserted to terminate by this relation. -/
inductive Executes (body : S → M W C E (ControlFlow S A)) : S → W → Run W C E A → Prop where
  | done (s : S) (w mid : W) (cs : List (W × C)) (a : A)
      (first : body s w = ⟨.ok (.done a),mid,cs⟩) : Executes body s w ⟨.ok a,mid,cs⟩
  | next (s next : S) (w mid : W) (cs : List (W × C)) (r : Run W C E A)
      (first : body s w = ⟨.ok (.cont next),mid,cs⟩)
      (tail : Executes body next mid r) :
      Executes body s w ⟨r.outcome,r.world,cs ++ r.calls⟩
  | fail (s : S) (w mid : W) (cs : List (W × C)) (e : E)
      (first : body s w = ⟨.fail e,mid,cs⟩) : Executes body s w ⟨.fail e,mid,cs⟩
  | diverge (s : S) (w mid : W) (cs : List (W × C))
      (first : body s w = ⟨.div,mid,cs⟩) : Executes body s w ⟨.div,mid,cs⟩

theorem finite_exact (body : S → M W C E (ControlFlow S A))
    {s : S} {w : W} {r : Run W C E A} (h : Executes body s w r) :
    ∃ n, fuel body n s w = r := by
  induction h with
  | done s w mid cs a first =>
    exact ⟨1,by simp only [fuel,PV_W_Threading.bind,first,PV_W_Threading.lift,List.append_nil]⟩
  | next s next w mid cs r first tail ih =>
    obtain ⟨n,eq⟩ := ih
    refine ⟨n+1,?_⟩
    simp only [fuel,PV_W_Threading.bind,first]
    rw [eq]
  | fail s w mid cs e first =>
    exact ⟨1,by simp only [fuel,PV_W_Threading.bind,first]⟩
  | diverge s w mid cs first =>
    exact ⟨1,by simp only [fuel,PV_W_Threading.bind,first]⟩

theorem fuel_valid (body : S → M W C E (ControlFlow S A))
    (step : W → C → W → Prop) (localLaw : ∀ s, Valid step (body s))
    (n : Nat) (s : S) : Valid step (fuel body n s) := by
  induction n generalizing s with
  | zero => exact valid_lift step .div
  | succ n ih =>
    apply valid_bind step _ _ (localLaw s)
    intro cf
    cases cf with
    | cont next => exact ih next
    | done a => exact valid_lift step (.ok a)

theorem execution_threaded (body : S → M W C E (ControlFlow S A))
    (step : W → C → W → Prop) (localLaw : ∀ s, Valid step (body s))
    {s : S} {w : W} {r : Run W C E A} (h : Executes body s w r) :
    Threaded step w r.calls r.world := by
  obtain ⟨n,eq⟩ := finite_exact body h
  rw [← eq]
  exact fuel_valid body step localLaw n s w

inductive SourceExecutes (body : S → Aeneas.Std.Result (ControlFlow S A)) :
    S → Aeneas.Std.Result A → Prop where
  | done (s : S) (a : A) (first : body s = .ok (.done a)) : SourceExecutes body s (.ok a)
  | next (s next : S) (r : Aeneas.Std.Result A) (first : body s = .ok (.cont next))
      (tail : SourceExecutes body next r) : SourceExecutes body s r
  | fail (s : S) (e : Aeneas.Std.Error) (first : body s = .fail e) : SourceExecutes body s (.fail e)
  | diverge (s : S) (first : body s = .div) : SourceExecutes body s .div

/-- Uses the pinned library's symbolic loop equation, never unfolds a large
concrete iteration. This is a finite source execution law, not native purity. -/
theorem source_loop (body : S → Aeneas.Std.Result (ControlFlow S A))
    {s : S} {r : Aeneas.Std.Result A} (h : SourceExecutes body s r) :
    Aeneas.Std.loop body s = r := by
  induction h with
  | done s a first => rw [Aeneas.Std.loop.eq_def,first]
  | next s next r first tail ih => rw [Aeneas.Std.loop.eq_def,first]; exact ih
  | fail s e first => rw [Aeneas.Std.loop.eq_def,first]
  | diverge s first => rw [Aeneas.Std.loop.eq_def,first]

#print axioms finite_exact
#print axioms fuel_valid
#print axioms execution_threaded
#print axioms source_loop
end R1Z.PV_W_Loops
