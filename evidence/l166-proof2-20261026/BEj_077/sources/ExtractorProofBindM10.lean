import ExtractorWorkMonad

/-! A generic proof-dependent option bind. Keeping its dependent match on a
generic value avoids specializing that match to a giant interpolation term
while the kernel checks the enclosing decoder definition. -/
set_option autoImplicit false
namespace AspisR1.ExtractorProofBindM10

@[noinline] def bind {A B : Type} (source : Option A) (x : Option A × Nat)
    (hv : x.1 = source) (next : ∀ a, source = some a → Option B × Nat) :
    Option B × Nat :=
  match hx : x.1 with
  | none => (none,x.2)
  | some a => let r := next a (hv.symm.trans hx); (r.1,x.2+r.2)

theorem value {A B : Type} (source : Option A) (x : Option A × Nat)
    (hv : x.1 = source) (next : ∀ a, source = some a → Option B × Nat) :
    (bind source x hv next).1 = source.pbind (fun a ha => (next a ha).1) := by
  rcases x with ⟨o,n⟩
  cases o <;> cases hv <;> rfl

theorem work {A B : Type} (source : Option A) (x : Option A × Nat)
    (hv : x.1 = source) (next : ∀ a, source = some a → Option B × Nat)
    (C D : Nat) (hx : x.2 ≤ C) (hn : ∀ a ha, (next a ha).2 ≤ D) :
    (bind source x hv next).2 ≤ C+D := by
  unfold bind
  split
  · exact hx.trans (Nat.le_add_right _ _)
  · rename_i a ha
    exact Nat.add_le_add hx (hn a (hv.symm.trans ha))

#print axioms value
#print axioms work
end AspisR1.ExtractorProofBindM10
