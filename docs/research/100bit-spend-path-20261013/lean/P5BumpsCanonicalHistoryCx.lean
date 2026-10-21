import Std

/-! A distinctly named P5 history interface. This is a source-audit target,
not an extraction of the SVM or a proof that arbitrary caller-selected s.P5
holds. Canonical search and ownership are parameters of the runtime model. -/
set_option autoImplicit false
namespace AspisR1.P5BumpsCanonicalHistoryCx

structure Image (Seed Key : Type) where
  seed : Seed
  key : Key
  bump : Nat

variable {Seed Key Payload : Type}

def Canonical (find : Seed → Key × Nat) (a : Image Seed Key) : Prop :=
  (a.key, a.bump) = find a.seed

/-- No initial controlled images; creation comes from canonical search;
updates may change arbitrary payload while preserving identity and bump. -/
inductive History (find : Seed → Key × Nat) : List (Image Seed Key × Payload) → Prop
  | empty : History find []
  | initialized {xs} (h : History find xs) (s : Seed) (p : Payload) :
      History find ((⟨s, (find s).1, (find s).2⟩, p) :: xs)
  | update {xs} (h : History find xs) (a : Image Seed Key)
      (old fresh : Payload) (hm : (a, old) ∈ xs) :
      History find ((a, fresh) :: xs)
  | remove {xs ys} (h : History find xs)
      (hsub : ∀ x, x ∈ ys → x ∈ xs) : History find ys

theorem canonical_of_history (find : Seed → Key × Nat)
    {xs : List (Image Seed Key × Payload)} (h : History find xs) :
    ∀ x, x ∈ xs → Canonical find x.1 := by
  induction h with
  | empty => intro x hm; cases hm
  | initialized h s p ih =>
      intro x hm
      rcases List.mem_cons.mp hm with he | hm
      · subst x
        exact Prod.eta (find s)
      · exact ih x hm
  | update h a old fresh hm ih =>
      intro x hx
      rcases List.mem_cons.mp hx with he | hx
      · subst x
        exact ih (a, old) hm
      · exact ih x hx
  | remove h hsub ih =>
      intro x hx
      exact ih x (hsub x hx)

/-- Hints need not be canonical input bytes: account provenance fixes the
accepted key, and a successful rederivation must agree with that key. -/
theorem hinted_identity_of_history (find : Seed → Key × Nat)
    (create : Seed → Nat → Option Key)
    {xs : List (Image Seed Key × Payload)} (h : History find xs)
    (a : Image Seed Key) (payload : Payload) (hm : (a, payload) ∈ xs)
    (hint : Nat) (checked : create a.seed hint = some a.key) :
    create a.seed hint = some (find a.seed).1 := by
  have hc := canonical_of_history find h (a, payload) hm
  have hk : a.key = (find a.seed).1 := congrArg Prod.fst hc
  exact checked.trans (congrArg some hk)

/-- The marker planner's successful equality check, independently of any
canonical bump or collision-resistance assumption. -/
theorem marker_checked_before_use (derive : Seed → Option Key)
    (s : Seed) (passed expected : Key)
    (derived : derive s = some expected) (checked : passed = expected) :
    derive s = some passed := by
  exact derived.trans (congrArg some checked.symm)

/-- A matching address does not prove highest-bump canonicality, even for an
injective create function; the two off-curve candidates are distinct. -/
theorem matching_is_not_canonical :
    ∃ (find : Unit → Nat × Nat) (create : Unit → Nat → Option Nat)
      (a : Image Unit Nat),
      create a.seed a.bump = some a.key ∧ ¬ Canonical find a := by
  refine ⟨fun _ => (2, 2), fun _ b => some b, ⟨(), 1, 1⟩, rfl, ?_⟩
  intro hc
  have : (1 : Nat) = 2 := congrArg Prod.fst hc
  cases this

/-- Replacing a read-only suffix of a disjunctive rejection predicate by an
arbitrary Boolean is a sound overapproximation for the checked prefix. -/
def addressGate (reject : Bool) : Except Unit Unit :=
  if reject then .error () else .ok ()

theorem prefix_gate_of_full (badPrefix tail : Bool)
    (accepted : addressGate (badPrefix || tail) = .ok ()) :
    addressGate badPrefix = .ok () := by
  cases badPrefix <;> cases tail <;> cases accepted <;> rfl

#print axioms prefix_gate_of_full
#print axioms canonical_of_history
#print axioms hinted_identity_of_history
#print axioms marker_checked_before_use
#print axioms matching_is_not_canonical
end AspisR1.P5BumpsCanonicalHistoryCx
