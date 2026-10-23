import Std
set_option autoImplicit false
namespace AspisR1.S2F

/-- Labels are caller source cuts; children keep their own internal histories. -/
inductive Step where
  | shape1 | accounts | distinct | readonlyProof | readonlyPublic | cpMetadata
  | cpAcquire | scan | publicAcquire | decode | validate | candidate
  | proofAcquire | proofEnd | proofGate | first | cpLength | copy | cleanup1
  | shape2 | clear | validateAsq8 | proofAcquire2 | cpAcquire2 | proofEnd2
  | proofLength2 | publicEncode | publicLength | second | emit | cleanup2
  deriving DecidableEq

def stage1Steps : List Step := [.shape1,.accounts,.distinct,.readonlyProof,
  .readonlyPublic,.cpMetadata,.cpAcquire,.scan,.publicAcquire,.decode,.validate,
  .candidate,.proofAcquire,.proofEnd,.proofGate,.first,.cpLength,.copy,.cleanup1]
def stage2Steps : List Step := [.shape2,.clear,.validateAsq8,.proofAcquire2,
  .cpAcquire2,.proofEnd2,.proofLength2,.publicEncode,.publicLength,.second,.emit,.cleanup2]

/-- Error and abort retain the already reached state, including effects. -/
inductive Outcome (Error State : Type) where
  | next : State → Outcome Error State
  | error : Error → State → Outcome Error State
  | abort : State → Outcome Error State

def run {E S : Type} (advance : Step → S → Outcome E S) : List Step → S → Outcome E S
  | [],s => .next s
  | p::ps,s => match advance p s with
    | .next t => run advance ps t
    | .error e t => .error e t
    | .abort t => .abort t

/-- Native and reference carriers may differ. Rel includes exact original inputs,
full typed heap/guard/allocator admission and child state when instantiated. -/
inductive Matches {E N R : Type} (rel : N → R → Prop) : Outcome E N → Outcome E R → Prop where
  | next {n : N} {r : R} : rel n r → Matches rel (.next n) (.next r)
  | error {e : E} {n : N} {r : R} : rel n r → Matches rel (.error e n) (.error e r)
  | abort {n : N} {r : R} : rel n r → Matches rel (.abort n) (.abort r)

/-- A local law, quantified over cut states. This is a proof obligation, not an
adopted assumption or a claim that finite Kani projections instantiate it. -/
def StepLaw {O E N R : Type} (rel : O → N → R → Prop)
    (native : Step → N → Outcome E N) (reference : Step → R → Outcome E R)
    (original : O) (step : Step) : Prop :=
  ∀ n r, rel original n r → Matches (rel original) (native step n) (reference step r)

/-- Composition preserves both normal and rejecting/aborting executions. No
terminal success or whole-program equality is a premise. -/
theorem sequence_simulation {O E N R : Type} (rel : O → N → R → Prop)
    (native : Step → N → Outcome E N) (reference : Step → R → Outcome E R)
    (original : O) (steps : List Step)
    (laws : ∀ step, step ∈ steps → StepLaw rel native reference original step)
    (n : N) (r : R) (initial : rel original n r) :
    Matches (rel original) (run native steps n) (run reference steps r) := by
  induction steps generalizing n r with
  | nil => exact Matches.next initial
  | cons step steps ih =>
    have law := laws step (by simp only [List.mem_cons, true_or]) n r initial
    have tail : ∀ p, p ∈ steps → StepLaw rel native reference original p := by
      intro p hp
      exact laws p (List.mem_cons_of_mem step hp)
    cases hn : native step n with
    | next n' =>
      cases hr : reference step r with
      | next r' =>
        rw [hn,hr] at law
        cases law with
        | next related => simpa only [run,hn,hr] using ih tail n' r' related
      | error e r' => rw [hn,hr] at law; cases law
      | abort r' => rw [hn,hr] at law; cases law
    | error e n' =>
      cases hr : reference step r with
      | next r' => rw [hn,hr] at law; cases law
      | error f r' =>
        rw [hn,hr] at law
        simpa only [run,hn,hr] using law
      | abort r' => rw [hn,hr] at law; cases law
    | abort n' =>
      cases hr : reference step r with
      | next r' => rw [hn,hr] at law; cases law
      | error f r' => rw [hn,hr] at law; cases law
      | abort r' =>
        rw [hn,hr] at law
        simpa only [run,hn,hr] using law

/-- Same fixed originals, same final error-free result. This does not provide
concrete source-step laws, an E evaluator port, or native execution admission. -/
theorem sequence_success {O E N R : Type} (rel : O → N → R → Prop)
    (native : Step → N → Outcome E N) (reference : Step → R → Outcome E R)
    (original : O) (steps : List Step)
    (laws : ∀ step, step ∈ steps → StepLaw rel native reference original step)
    (n : N) (r : R) (initial : rel original n r) (final : N)
    (accepted : run native steps n = .next final) :
    ∃ finalReference, run reference steps r = .next finalReference ∧
      rel original final finalReference := by
  have joined := sequence_simulation rel native reference original steps laws n r initial
  rw [accepted] at joined
  cases hr : run reference steps r with
  | next finalReference =>
    rw [hr] at joined
    cases joined with
    | next related => exact ⟨finalReference,rfl,related⟩
  | error e s => rw [hr] at joined; cases joined
  | abort s => rw [hr] at joined; cases joined

/-- Every successful source cut has a paired reference successor, from the same
fixed originals. Error cleanup must be included in the actual error state;
this relation does not invent a normal cleanup after an abort. -/
inductive PairedCuts {O E N R : Type} (rel : O → N → R → Prop)
    (native : Step → N → Outcome E N) (reference : Step → R → Outcome E R)
    (original : O) : List Step → N → R → N → R → Prop where
  | nil {n : N} {r : R} : rel original n r → PairedCuts rel native reference original [] n r n r
  | cons {p : Step} {ps : List Step} {n n' nf : N} {r r' rf : R} :
      rel original n r → native p n = .next n' → reference p r = .next r' →
      PairedCuts rel native reference original ps n' r' nf rf →
      PairedCuts rel native reference original (p::ps) n r nf rf

/-- Constructs the intermediate paired cuts, rather than assuming them. The
local laws still require concrete native/reference implementations and proofs. -/
theorem paired_success {O E N R : Type} (rel : O → N → R → Prop)
    (native : Step → N → Outcome E N) (reference : Step → R → Outcome E R)
    (original : O) (steps : List Step)
    (laws : ∀ step, step ∈ steps → StepLaw rel native reference original step)
    (n : N) (r : R) (initial : rel original n r) (final : N)
    (accepted : run native steps n = .next final) :
    ∃ finalReference, PairedCuts rel native reference original steps n r final finalReference := by
  induction steps generalizing n r with
  | nil => cases accepted; exact ⟨r,PairedCuts.nil initial⟩
  | cons p ps ih =>
    have law := laws p (by simp only [List.mem_cons,true_or]) n r initial
    have tail : ∀ step, step ∈ ps → StepLaw rel native reference original step := by
      intro step member
      exact laws step (List.mem_cons_of_mem p member)
    cases hn : native p n with
    | error error state => simp only [run,hn] at accepted; cases accepted
    | abort state => simp only [run,hn] at accepted; cases accepted
    | next n' =>
      simp only [run,hn] at accepted
      cases hr : reference p r with
      | error error state => rw [hn,hr] at law; cases law
      | abort state => rw [hn,hr] at law; cases law
      | next r' =>
        rw [hn,hr] at law
        cases law with
        | next related =>
          obtain ⟨rf,joined⟩ := ih tail n' r' related accepted
          exact ⟨rf,PairedCuts.cons initial hn hr joined⟩

#print axioms paired_success

#print axioms sequence_simulation
#print axioms sequence_success
end AspisR1.S2F
