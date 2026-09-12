import Std
set_option autoImplicit false

/-! Deterministic scalar layer of performance_verifier::semantic.
No independently supplied Semantic/Program state is accepted. The initial
claim and all compact response coefficients are read from the same field word.
The arithmetic operations are explicit parameters: instantiation to canonical
QM31, byte parsing, real transcript samplers, and the selected payment terminal
are NOT claimed in this leaf. -/
namespace AspisV8Completion.SemanticWireExecution
universe u
variable {K : Type u}

structure Arithmetic (K : Type u) where
  zero : K
  add : K → K → K
  sub : K → K → K
  mul : K → K → K
  square : K → K
  sumProducts3 : (Fin 3 → K) → (Fin 3 → K) → K

abbrev Word (K : Type u) := Fin 697 → K

def sentIndex (r : Fin 10) (j : Fin 27) : Fin 697 :=
  ⟨1 + 27 * r.val + j.val, by omega⟩

def pointIndex (i : Fin 84) : Fin 697 :=
  ⟨271 + (i.val / 28) * 29 + i.val % 28, by omega⟩

def sent (w : Word K) (r : Fin 10) (j : Fin 27) : K := w (sentIndex r j)
def pointClaims (w : Word K) (i : Fin 84) : K := w (pointIndex i)

/-- c0 is transmitted, c1 is reconstructed, and c2..c27 are transmitted.
The tail sum starts at zero, matching performance_verifier (not its diagnostic
inactive_row_binding variant's differently associated sum). -/
def polynomial (ops : Arithmetic K) (prior : K) (message : Fin 27 → K) : Fin 28 → K :=
  let tail := ((List.finRange 26).map (fun i => message ⟨i.val+1, by omega⟩)).foldl ops.add ops.zero
  fun i => if h0 : i.val = 0 then message 0
    else if h1 : i.val = 1 then ops.sub prior (ops.add (ops.add (message 0) (message 0)) tail)
    else message ⟨i.val-1, by omega⟩

/-- Seven four-coefficient blocks, matching the selected core evaluator.
Prepared multiplication and the mixed-width sum kernel need their existing
arithmetic refinements when instantiated; no such equalities are assumed here. -/
def evaluate (ops : Arithmetic K) (poly : Fin 28 → K) (alpha : K) : K :=
  let x2 := ops.square alpha
  let x3 := ops.mul alpha x2
  let x4 := ops.square x2
  let powers : Fin 3 → K := fun i => if i.val = 0 then alpha else if i.val = 1 then x2 else x3
  let block : Fin 7 → K := fun b => ops.add (poly ⟨4*b.val, by omega⟩)
    (ops.sumProducts3 powers (fun i => poly ⟨4*b.val+i.val+1, by omega⟩))
  ((List.finRange 6).reverse).foldl
    (fun acc b => ops.add (ops.mul x4 acc) (block ⟨b.val, by omega⟩)) (block 6)

def step (ops : Arithmetic K) (w : Word K) (coins : Fin 10 → K)
    (prior : K) (round : Fin 10) : K :=
  evaluate ops (polynomial ops prior (sent w round)) (coins round)

/-- Computes, rather than assumes, the carried semantic claim. -/
def carried (ops : Arithmetic K) (w : Word K) (coins : Fin 10 → K)
    (rounds : List (Fin 10)) : K := rounds.foldl (step ops w coins) (w 0)

def terminalInput (ops : Arithmetic K) (w : Word K) (coins : Fin 10 → K) :
    K × (Fin 84 → K) :=
  (carried ops w coins (List.finRange 10), pointClaims w)

theorem transmitted_zero (ops : Arithmetic K) (prior : K) (m : Fin 27 → K) :
    polynomial ops prior m 0 = m 0 := by simp [polynomial]

theorem transmitted_tail (ops : Arithmetic K) (prior : K) (m : Fin 27 → K)
    (i : Fin 28) (h : 2 ≤ i.val) :
    polynomial ops prior m i = m ⟨i.val-1, by omega⟩ := by
  have h0 : i ≠ 0 := by intro hz; subst i; simp at h
  simp [polynomial, h0, show i.val ≠ 1 by omega]

/-- Source dependency fact, not an assumption of semantic acceptance. -/
theorem sent_before_point_claims (r : Fin 10) (j : Fin 27) :
    (sentIndex r j).val < 271 := by simp [sentIndex]; omega

theorem terminal_projection_excludes_D (i : Fin 84) :
    (pointIndex i).val < 358 ∧ ((pointIndex i).val - 271) % 29 < 28 := by
  simp only [pointIndex]
  omega

/-- Recursive noninterference: ANY continuation uses only the rounds it
actually consumes, not a completed final proof or future coins. -/
theorem fold_same (ops : Arithmetic K) (w v : Word K) (a b : Fin 10 → K)
    (rounds : List (Fin 10)) (x y : K) (initial : x = y)
    (messages : ∀ r ∈ rounds, sent w r = sent v r)
    (coins : ∀ r ∈ rounds, a r = b r) :
    rounds.foldl (step ops w a) x = rounds.foldl (step ops v b) y := by
  induction rounds generalizing x y with
  | nil => exact initial
  | cons r rs ih =>
    apply ih
    · simp only [step, initial, messages r (by simp), coins r (by simp)]
    · intro s hs; exact messages s (by simp [hs])
    · intro s hs; exact coins s (by simp [hs])

/-- For a fixed realised challenge sequence, every semantic prefix is
constructed from the same word. Unread fields cannot affect the computation.
This does not assert that actual FS challenges stay fixed after a mutation. -/
theorem semantic_prefix_independent (ops : Arithmetic K) (w v : Word K)
    (a b : Fin 10 → K) (cut : Nat)
    (initial : w 0 = v 0)
    (messages : ∀ r ∈ (List.finRange 10).take cut, sent w r = sent v r)
    (coins : ∀ r ∈ (List.finRange 10).take cut, a r = b r) :
    carried ops w a ((List.finRange 10).take cut) =
      carried ops v b ((List.finRange 10).take cut) :=
  fold_same ops w v a b _ _ _ initial messages coins

/-- Suffix/OOD/relation changes cannot leave a stale caller-supplied semantic
state: this constructor is recomputed from precisely its consumed fields. -/
theorem suffix_independent (ops : Arithmetic K) (w v : Word K) (coins : Fin 10 → K)
    (same : ∀ i : Fin 697, i.val < 358 → w i = v i) :
    terminalInput ops w coins = terminalInput ops v coins := by
  apply Prod.ext
  · apply fold_same
    · exact same 0 (by decide)
    · intro r _; funext j
      exact same (sentIndex r j) (by have := sent_before_point_claims r j; omega)
    · intro r _; rfl
  · funext i
    exact same (pointIndex i) (terminal_projection_excludes_D i).1

#print axioms fold_same
#print axioms semantic_prefix_independent
#print axioms suffix_independent
#print axioms terminal_projection_excludes_D
end AspisV8Completion.SemanticWireExecution
