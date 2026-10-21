import R1Z.GamesR1

/-! Abstract writer composition. Primitive tariffs are an oracle RAM model,
not a certificate for arbitrary Lean functions or an allocator. -/
set_option autoImplicit false
namespace R1Z.SimCostWriter
abbrev Costed (A : Type) := A × Nat

def pure {A : Type} (a : A) : Costed A := (a, 0)
def tick (n : Nat) : Costed Unit := ((), n)
def bind {A B : Type} (a : Costed A) (f : A → Costed B) : Costed B :=
  let b := f a.1
  (b.1, a.2 + b.2)

theorem erase_bind {A B : Type} (a : Costed A) (f : A → Costed B) :
    (bind a f).1 = (f a.1).1 := rfl

theorem cost_bind {A B : Type} (a : Costed A) (f : A → Costed B) :
    (bind a f).2 = a.2 + (f a.1).2 := rfl

/-- Refinement is indexed by the reference function, so composition never
unfolds the bodies of reference stages (M10 pass 7 pattern). -/
structure Stage {A B : Type} (reference : A → B) (budget : Nat) where
  run : A → Costed B
  erase : ∀ a, (run a).1 = reference a
  bound : ∀ a, (run a).2 ≤ budget

def seq {A B C : Type} {f : A → B} {g : B → C} {m n : Nat}
    (s : Stage f m) (t : Stage g n) : Stage (fun a => g (f a)) (m+n) where
  run a := bind (s.run a) t.run
  erase a := by rw [erase_bind, t.erase, s.erase]
  bound a := Nat.add_le_add (s.bound a) (t.bound (s.run a).1)

theorem seq_erase {A B C : Type} {f : A → B} {g : B → C} {m n : Nat}
    (s : Stage f m) (t : Stage g n) (a : A) :
    ((seq s t).run a).1 = g (f a) := (seq s t).erase a

theorem seq_bound {A B C : Type} {f : A → B} {g : B → C} {m n : Nat}
    (s : Stage f m) (t : Stage g n) (a : A) :
    ((seq s t).run a).2 ≤ m+n := (seq s t).bound a

/-- Fixed-width primitive instruction vocabulary. M31 is one 32-bit word,
QM31 four; samples are uniform primitive calls, not rejection loops. -/
inductive Primitive
  | sampleWord | m31Add | m31Mul | qm31Add | qm31Mul | program | insert
  deriving DecidableEq

def tariff : Primitive → Nat
  | .sampleWord => 1
  | .m31Add => 1
  | .m31Mul => 1
  | .qm31Add => 4
  | .qm31Mul => 32
  | .program => 1
  | .insert => 1

theorem tariff_bound (p : Primitive) : tariff p ≤ 32 := by cases p <;> decide

#print axioms erase_bind
#print axioms cost_bind
#print axioms seq_erase
#print axioms seq_bound
#print axioms tariff_bound
end R1Z.SimCostWriter
