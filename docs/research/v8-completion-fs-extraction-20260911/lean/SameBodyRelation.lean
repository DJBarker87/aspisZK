import Std
set_option autoImplicit false

/-! Causal relation-message producer and executable same-word checks.
This is NOT the complete payment verifier or the historical Program endpoint.
Queries/increment and transcript coins remain explicit environment inputs.
Unlike retrospective constant-body callbacks, each message is stored before
the continuation receiving its next challenge exists in the execution.
-/
namespace AspisV8Completion.SameBodyRelation
universe u v
variable {K : Type u} {Schedule : Type v}
abbrev Word (K : Type u) := Fin 697 → K
abbrev Sent (K : Type u) := Fin 6 → K
abbrev Final (K : Type u) := Fin 256 → K

instance finiteFunctionDecidableEq [DecidableEq K] (n : Nat) : DecidableEq (Fin n → K) :=
  fun f g => if h : ∀ i, f i = g i then isTrue (funext h)
    else isFalse (fun eq => h (fun i => congrFun eq i))

abbrev responseIndex (r : Fin 4) (j : Fin 6) : Fin 697 :=
  ⟨417 + 6*r.val+j.val, by omega⟩
def finalIndex (j : Fin 256) : Fin 697 := ⟨441+j.val, by omega⟩
def response (w : Word K) (r : Fin 4) : Sent K := fun j => w (responseIndex r j)
def finalValues (w : Word K) : Final K := fun j => w (finalIndex j)

/-- Serialization after a causal run, not a way of deriving a strategy from
an already completed body. The earlier 417 fields are preserved literally. -/
def assemble (early : Fin 417 → K) (rounds : Fin 4 → Sent K) (final : Final K) : Word K :=
  fun i => if h : i.val < 417 then early ⟨i.val, h⟩
    else if h' : i.val < 441 then
      rounds ⟨(i.val-417)/6, by omega⟩ ⟨(i.val-417)%6, Nat.mod_lt _ (by decide)⟩
    else final ⟨i.val-441, by omega⟩

theorem assembled_responses (early : Fin 417 → K) (rounds : Fin 4 → Sent K)
    (final : Final K) (r : Fin 4) : response (assemble early rounds final) r = rounds r := by
  funext j
  have hj := j.isLt
  have hr := r.isLt
  have hdiv : (417 + 6*r.val+j.val-417)/6 = r.val := by omega
  have hmod : (417 + 6*r.val+j.val-417)%6 = j.val := by omega
  simp only [response, assemble, responseIndex, Fin.val_mk]
  rw [dif_neg (show ¬417+6*r.val+j.val<417 by omega)]
  rw [dif_pos (show 417+6*r.val+j.val<441 by omega)]
  exact congr (congrArg rounds (Fin.ext hdiv)) (Fin.ext hmod)

theorem assembled_final (early : Fin 417 → K) (rounds : Fin 4 → Sent K)
    (final : Final K) : finalValues (assemble early rounds final) = final := by
  funext j
  simp [finalValues, assemble, finalIndex, show ¬441+j.val<417 by omega,
    show ¬441+j.val<441 by omega]

theorem assembled_early (early : Fin 417 → K) (rounds : Fin 4 → Sent K)
    (final : Final K) (i : Fin 417) :
    assemble early rounds final ⟨i.val, by omega⟩ = early i := by
  simp [assemble, i.isLt]

/-- Each compact response is fixed before its alpha; later messages may
depend on every preceding challenge through nested continuations. -/
inductive Tail (K : Type u) : Nat → Type u where
  | done : Tail K 0
  | round {n : Nat} (sent : Sent K) (next : K → Tail K n) : Tail K (n+1)

structure FinalStage (K : Type u) (Schedule : Type v) where
  final256 : Final K
  afterQueries : Schedule → K → Tail K 3

structure FirstStage (K : Type u) (Schedule : Type v) where
  response0 : Sent K
  afterAlpha0 : K → FinalStage K Schedule

/-- This producer is created at the pre-tau boundary. No alpha, queries, rho,
or final argument is available at that boundary. Its legal adversarial code
may depend on the already fixed pre-tau state. Source coupling must construct
that state and this strategy uniformly, not choose one per completed run. -/
abbrev Strategy (K : Type u) (Schedule : Type v) := K → FirstStage K Schedule

structure Arithmetic (K : Type u) where
  sub : K → K → K
  quarter : K → K
  evaluate7 : (Fin 7 → K) → K → K

/-- Literal omitted-c4 reconstruction; no boundary acceptance assumed. -/
def compact (ops : Arithmetic K) (claim : K) (m : Sent K) : Fin 7 → K :=
  fun i => if h : i.val < 4 then m ⟨i.val, by omega⟩
    else if i.val = 4 then ops.sub (ops.quarter claim) (m 0)
    else m ⟨i.val-1, by omega⟩

def tailMessages : {n : Nat} → Tail K n → (Fin n → K) → List (Sent K)
  | 0, .done, _ => []
  | n+1, .round m next, coins => m :: tailMessages (next (coins 0)) (fun i => coins i.succ)

def tailClaim (ops : Arithmetic K) : {n : Nat} → Tail K n → (Fin n → K) → K → K
  | 0, .done, _, c => c
  | n+1, .round m next, coins, c =>
      tailClaim ops (next (coins 0)) (fun i => coins i.succ)
        (ops.evaluate7 (compact ops c m) (coins 0))

def laterResponses (w : Word K) : List (Sent K) := [response w 1, response w 2, response w 3]

def roundsOfTail (first : Sent K) (tail : Tail K 3) (coins : Fin 3 → K) : Fin 4 → Sent K :=
  match tail with
  | .round m1 n1 => match n1 (coins 0) with
    | .round m2 n2 => match n2 (coins 1) with
      | .round m3 _ => fun r => if r.val=0 then first else if r.val=1 then m1
        else if r.val=2 then m2 else m3

def produce (early : Fin 417 → K) (strategy : Strategy K Schedule)
    (tau alpha0 : K) (queries : Schedule) (rho : K) (coins : Fin 3 → K) : Word K :=
  let first := strategy tau
  let final := first.afterAlpha0 alpha0
  assemble early (roundsOfTail first.response0 (final.afterQueries queries rho) coins) final.final256

structure Result (K : Type u) where
  firstClaim : K
  final256 : Final K
  terminalClaim : K

/-- Checks the SAME submitted word at each consumed-message boundary. The
query increment is an explicit unresolved source interface: this definition
does not identify it with the genuine opened-query computation. -/
def consume [DecidableEq K] (ops : Arithmetic K) (strategy : Strategy K Schedule)
    (w : Word K) (tau alpha0 : K) (queries : Schedule) (rho : K)
    (laterCoins : Fin 3 → K) (ordinary : K) (increment : Final K → Schedule → K → K) :
    Option (Result K) :=
  let first := strategy tau
  if first.response0 ≠ response w 0 then none else
  let final := first.afterAlpha0 alpha0
  if final.final256 ≠ finalValues w then none else
  let tail := final.afterQueries queries rho
  if tailMessages tail laterCoins ≠ laterResponses w then none else
  let c := ops.evaluate7 (compact ops ordinary first.response0) alpha0
  some ⟨c, final.final256,
    tailClaim ops tail laterCoins (ops.sub c (increment final.final256 queries rho))⟩

/-- These equalities are OUTPUTS of checked consumption, not supplied
coherence fields. They do not assert actual Rust success or ideal acceptance. -/
theorem consume_constructs_correspondence [DecidableEq K]
    (ops : Arithmetic K) (strategy : Strategy K Schedule) (w : Word K)
    (tau alpha0 : K) (queries : Schedule) (rho : K) (coins : Fin 3 → K)
    (ordinary : K) (inc : Final K → Schedule → K → K) (result : Result K)
    (success : consume ops strategy w tau alpha0 queries rho coins ordinary inc = some result) :
    (strategy tau).response0 = response w 0 ∧
    ((strategy tau).afterAlpha0 alpha0).final256 = finalValues w ∧
    tailMessages (((strategy tau).afterAlpha0 alpha0).afterQueries queries rho) coins =
      laterResponses w ∧
    result.final256 = finalValues w := by
  simp only [consume] at success
  split at success
  · contradiction
  next h0 =>
    split at success
    · contradiction
    next hf =>
      split at success
      · contradiction
      next ht =>
        have hresult := Option.some.inj success
        subst result
        exact ⟨Classical.not_not.mp h0, Classical.not_not.mp hf,
          Classical.not_not.mp ht, Classical.not_not.mp hf⟩

theorem produced_consumes [DecidableEq K] (ops : Arithmetic K)
    (early : Fin 417 → K) (strategy : Strategy K Schedule) (tau alpha0 : K)
    (queries : Schedule) (rho : K) (coins : Fin 3 → K) (ordinary : K)
    (inc : Final K → Schedule → K → K) :
    (consume ops strategy (produce early strategy tau alpha0 queries rho coins)
      tau alpha0 queries rho coins ordinary inc).isSome = true := by
  unfold produce consume
  simp only [assembled_responses, assembled_final, laterResponses]
  cases h1 : ((strategy tau).afterAlpha0 alpha0).afterQueries queries rho with
  | round m1 n1 =>
    cases h2 : n1 (coins 0) with
    | round m2 n2 =>
      cases h3 : n2 (coins 1) with
      | round m3 n3 =>
        cases h4 : n3 (coins 2)
        simp [roundsOfTail, tailMessages, h2, h3, h4,
          show (3 : Fin 4).val = 3 from rfl]

/-- Legal continuations sharing a prefix have exactly the same already-sent
messages even when their next and later challenge values differ. -/
theorem tail_head_fixed {n : Nat} (m : Sent K) (next : K → Tail K n)
    (a b : Fin (n+1) → K) :
    (tailMessages (.round m next) a).head? =
      (tailMessages (.round m next) b).head? := rfl

theorem tail_prefix_noninterference {n : Nat} (p : Tail K n)
    (a b : Fin n → K) (cut : Nat)
    (same : ∀ i : Fin n, i.val < cut → a i = b i) :
    (tailMessages p a).take cut = (tailMessages p b).take cut := by
  induction p generalizing cut with
  | done => rfl
  | @round n m next ih =>
    cases cut with
    | zero => rfl
    | succ c =>
      have h0 : a 0 = b 0 := same 0 (by simp)
      simp only [tailMessages, List.take_succ_cons, h0]
      congr 1
      apply ih (b 0) _ _ c
      intro i hi
      exact same i.succ (by simpa using Nat.succ_lt_succ hi)

#print axioms consume_constructs_correspondence
#print axioms tail_prefix_noninterference
#print axioms assembled_responses
#print axioms assembled_final
#print axioms produced_consumes
end AspisV8Completion.SameBodyRelation
