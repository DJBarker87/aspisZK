import Std
set_option autoImplicit false
namespace R1Z.PDict_TapeCore244

/-- Reply contents are unconstrained: errors and successful replies consume the
same cursor. There is no reset at a caller, retry, or rejection boundary. -/
structure Tape (A : Type) where
  replies : List A
  used : Nat

def read {A : Type} (t : Tape A) : Option (A × Tape A) :=
  match t.replies[t.used]? with
  | none => none
  | some reply => some (reply, { t with used := t.used + 1 })

def reads {A : Type} : Nat → Tape A → Option (List A × Tape A)
  | 0, t => some ([], t)
  | n+1, t => do
    let (reply, next) ← read t
    let (rest, final) ← reads n next
    some (reply :: rest, final)

theorem read_at {A : Type} (t : Tape A) (reply : A)
    (h : t.replies[t.used]? = some reply) :
    read t = some (reply, { t with used := t.used + 1 }) := by
  simp only [read, h]

theorem read_success {A : Type} (t next : Tape A) (reply : A)
    (run : read t = some (reply, next)) :
    t.replies[t.used]? = some reply ∧
      next.replies = t.replies ∧ next.used = t.used + 1 := by
  cases h : t.replies[t.used]? with
  | none => simp [read, h] at run
  | some value =>
    have eq : (value, {t with used := t.used+1}) = (reply, next) :=
      Option.some.inj (by simpa only [read, h] using run)
    cases eq
    exact ⟨rfl, rfl, rfl⟩

theorem read_exhausted {A : Type} (t : Tape A)
    (h : t.replies[t.used]? = none) : read t = none := by
  simp only [read, h]

theorem reads_inventory {A : Type} (n : Nat) (t final : Tape A) (out : List A)
    (run : reads n t = some (out, final)) :
    final.replies = t.replies ∧ final.used = t.used+n ∧ out.length = n := by
  induction n generalizing t final out with
  | zero =>
    have eq : ([],t) = (out,final) := Option.some.inj run
    cases eq
    exact ⟨rfl, by omega, rfl⟩
  | succ n ih =>
    cases hr : read t with
    | none => simp [reads, hr] at run
    | some pair =>
      rcases pair with ⟨value,next⟩
      cases hs : reads n next with
      | none => simp [reads, hr, hs] at run
      | some pair =>
        rcases pair with ⟨rest,last⟩
        have eq : value::rest = out ∧ last = final := by
          simpa [reads, hr, hs] using run
        obtain ⟨_,same,used⟩ := read_success t next value hr
        obtain ⟨same',used',length⟩ := ih next last rest hs
        rw [← eq.1, ← eq.2]
        exact ⟨same'.trans same, by omega, by simp only [List.length_cons, length]⟩

#print axioms read_at
#print axioms read_success
#print axioms read_exhausted
#print axioms reads_inventory
end R1Z.PDict_TapeCore244
