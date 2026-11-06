import NLF_WrapperLaws
set_option autoImplicit false
namespace NLF_ParentModel
open NLF_RefCell NLF_SdkModel

def HasToken (c : Cell Payload) (t : Nat) : Prop := c.writer = some t ∨ t ∈ c.readers

def ValidState (s : State) : Prop := ∀ i, Valid (s.cells i)
/-- Every allocated identity is globally fresh. No ABA token reuse after drop. -/
def Below (s : State) (next : Nat) : Prop := ∀ i t, HasToken (s.cells i) t → t < next

def Unique (s : State) : Prop :=
  ∀ i j t, HasToken (s.cells i) t → HasToken (s.cells j) t → i = j

inductive Event where
  | acquire (account token : Nat) (kind : Kind) (reply : Except ProgramError Guard)
  | deref (guard : Guard) (reply : Except Error Payload)
  | release (guard : Guard) (reply : Except Error Unit)
structure Parent where
  state : State
  next : Nat
  events : List Event

def Invariant (p : Parent) : Prop := ValidState p.state ∧ Below p.state p.next ∧ Unique p.state

def acquire (p : Parent) (a : Nat) (k : Kind) : Parent × Except ProgramError Guard :=
  let r := wrap p.state (p.state.accounts a).data p.next k
  (⟨r.1,p.next+1,p.events ++ [.acquire a p.next k r.2]⟩,r.2)

instance liveDecidable {α : Type} (c : Cell α) (t : Nat) (k : Kind) : Decidable (live c t k) := by
  cases k <;> dsimp [live] <;> infer_instance

def deref (p : Parent) (g : Guard) : Parent × Except Error Payload :=
  let r := if live (p.state.cells g.cell) g.token g.kind then .ok (NLF_SdkModel.deref p.state g)
           else .error .invalidToken
  (⟨p.state,p.next,p.events ++ [.deref g r]⟩,r)

def release (p : Parent) (g : Guard) : Parent × Except Error Unit :=
  match NLF_SdkModel.release p.state g with
  | .error e => (⟨p.state,p.next,p.events ++ [.release g (.error e)]⟩,.error e)
  | .ok s => (⟨s,p.next,p.events ++ [.release g (.ok ())]⟩,.ok ())

theorem fresh (s : State) (n i : Nat) (h : Below s n) :
    n ∉ (s.cells i).readers ∧ (s.cells i).writer ≠ some n := by
  constructor
  · intro hn; exact (Nat.lt_irrefl n) (h i n (Or.inr hn))
  · intro hn; exact (Nat.lt_irrefl n) (h i n (Or.inl hn))

theorem put_valid (s : State) (i : Nat) (c : Cell Payload)
    (h : ValidState s) (v : Valid c) : ValidState (put s i c) := by
  intro j; by_cases eq : j=i
  · subst j; simpa [put] using v
  · simpa [put,eq] using h j

theorem deref_frame (p : Parent) (g : Guard) :
    (deref p g).1.state = p.state ∧ (deref p g).1.next = p.next := by
  simp [deref]

theorem deref_invariant (p : Parent) (g : Guard) (h : Invariant p) :
    Invariant (deref p g).1 := by simpa [Invariant, deref] using h

#print axioms fresh
#print axioms put_valid
#print axioms deref_frame
#print axioms deref_invariant
end NLF_ParentModel
