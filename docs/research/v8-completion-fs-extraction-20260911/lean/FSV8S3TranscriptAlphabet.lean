import FSV8S3ScriptQueryAlphabet

/-! S3 FIRST-ATTEMPT SOURCE MODULE. Uncompiled in the preparation environment.
Check the pinned source, proof statement, and transitive axioms before promotion. -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000
set_option maxRecDepth 2000

namespace AspisV8Completion.FSV8S3TranscriptAlphabet
open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open FSV8S3ScriptQueryAlphabet

/-- Padding a static allowance performs no extra queries and does not alter
the query grammar. These are proofs about the actual imported constructors. -/
theorem queries_promote {A : Type} (P : List UInt8 → Prop) :
    ∀ {n} (p : Script (List UInt8) Block A n),
      QueriesIn P p → QueriesIn P (promote p) := by
  intro n p
  induction p with
  | done => intro _; trivial
  | abort => intro _; trivial
  | ask input next ih =>
    intro safe
    exact ⟨safe.1, fun a => ih a (safe.2 a)⟩

theorem queries_pad {A : Type} (P : List UInt8 → Prop) {n}
    (p : Script (List UInt8) Block A n) (safe : QueriesIn P p) :
    ∀ extra, QueriesIn P (pad p extra) := by
  intro extra
  induction extra with
  | zero => exact safe
  | succ extra ih => exact queries_promote P _ ih

theorem queries_bind {A B : Type} (P : List UInt8 → Prop) {m} :
    ∀ {n} (p : Script (List UInt8) Block A n)
      (next : A → Script (List UInt8) Block B m),
      QueriesIn P p → (∀ a, QueriesIn P (next a)) →
      QueriesIn P (bind p next) := by
  intro n p
  induction p with
  | done a =>
    intro next _ safeNext
    exact queries_pad P (next a) (safeNext a) _
  | abort => intro _ _ _; trivial
  | ask input response ih =>
    intro next safe safeNext
    exact ⟨safe.1, fun answer => ih answer next (safe.2 answer) safeNext⟩

theorem queries_map {A B : Type} (P : List UInt8 → Prop) (f : A → B) :
    ∀ {n} (p : Script (List UInt8) Block A n),
      QueriesIn P p → QueriesIn P (FSTranscriptScript.map f p) := by
  intro n p
  induction p with
  | done => intro _; trivial
  | abort => intro _; trivial
  | ask input next ih => intro safe; exact ⟨safe.1, fun a => ih a (safe.2 a)⟩

theorem queries_absorb (P : List UInt8 → Prop) (d : Block) (label : UInt8)
    (payload : List UInt8) (allowed : P (List.ofFn d ++ [0,label] ++ payload)) :
    QueriesIn P (absorbScript d label payload) := ⟨allowed, fun _ => trivial⟩

theorem queries_squeeze (P : List UInt8 → Prop) (d : Block)
    (out : P (List.ofFn d ++ [1])) (adv : P (List.ofFn d ++ [2])) :
    QueriesIn P (squeezeScript d) :=
  ⟨out, fun _ => ⟨adv, fun _ => trivial⟩⟩

/-- The real bounded ordinary decoder cannot invent an absorb marker. Its
control flow changes only how many duplex queries are actually performed. -/
theorem queries_word (P : List UInt8 → Prop)
    (out : ∀ d : Block, P (List.ofFn d ++ [1]))
    (adv : ∀ d : Block, P (List.ofFn d ++ [2]))
    (d : Block) (remaining : List Nat) : QueriesIn P (wordScript d remaining) := by
  cases remaining with
  | nil =>
    exact queries_map P _ _ (queries_squeeze P d (out d) (adv d))
  | cons => trivial

theorem queries_limb (P : List UInt8 → Prop)
    (out : ∀ d : Block, P (List.ofFn d ++ [1]))
    (adv : ∀ d : Block, P (List.ofFn d ++ [2])) :
    ∀ tries d remaining, QueriesIn P (limbScript tries d remaining) := by
  intro tries
  induction tries with
  | zero => intro _ _; trivial
  | succ tries ih =>
    intro d remaining
    apply queries_bind P _ _ (queries_word P out adv d remaining)
    intro step
    split
    · exact ih _ _
    · trivial

theorem queries_limbs (P : List UInt8 → Prop)
    (out : ∀ d : Block, P (List.ofFn d ++ [1]))
    (adv : ∀ d : Block, P (List.ofFn d ++ [2])) :
    ∀ count d remaining, QueriesIn P (limbsScript count d remaining) := by
  intro count
  induction count with
  | zero => intro _ _; trivial
  | succ count ih =>
    intro d remaining
    apply queries_bind P _ _ (queries_limb P out adv 8 d remaining)
    intro step
    cases step.1 with
    | none => trivial
    | some value => exact queries_map P _ _ (ih _ _)

theorem queries_challenge (P : List UInt8 → Prop)
    (out : ∀ d : Block, P (List.ofFn d ++ [1]))
    (adv : ∀ d : Block, P (List.ofFn d ++ [2])) (d : Block) :
    QueriesIn P (challengeScript d) := by
  apply queries_bind P _ _ (queries_squeeze P d (out d) (adv d))
  intro block
  exact queries_map P _ _ (queries_limbs P out adv 4 block.2 (words block.1))

#print axioms queries_bind
#print axioms queries_absorb
#print axioms queries_challenge
end AspisV8Completion.FSV8S3TranscriptAlphabet
