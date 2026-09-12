import SameBodyRelation
set_option autoImplicit false
namespace AspisV8Completion.SameBodyQueryClaim
open SameBodyRelation
universe u v
variable {K : Type u} {Schedule : Type v}

/-- Scalar operations only. Neither authentication nor a field law is an input
disguised as acceptance. Machine-QM31 refinement remains separate. -/
structure Arithmetic (K : Type u) extends SameBodyRelation.Arithmetic K where
  zero : K
  add : K → K → K
  mul : K → K → K

/-- Literal forward powers from relation_callback::inject, beginning at rho.
The values are already computed opened quotient/fold values, NOT final256
evaluations. Their source/authentication producer is still required. -/
def powersFrom (ops : Arithmetic K) (rho power : K) : Nat → List K
  | 0 => []
  | n+1 => power :: powersFrom ops rho (ops.mul power rho) n

def scales (ops : Arithmetic K) (rho : K) (n : Nat) : List K :=
  powersFrom ops rho rho n

def dot (ops : Arithmetic K) (a b : List K) : K :=
  (a.zip b).foldl (fun s pair => ops.add s (ops.mul pair.1 pair.2)) ops.zero

def increment (ops : Arithmetic K) (rho : K) (opened : Fin 22 → K) : K :=
  dot ops (scales ops rho 22) (List.ofFn opened)

/-- Rust adds inc to the running scalar while adding its line covector.
Subtraction appears in the discrepancy, not in this scalar update. -/
def injectClaim (ops : Arithmetic K) (prior rho : K) (opened : Fin 22 → K) : K :=
  ops.add prior (increment ops rho opened)

def afterQuery (ops : Arithmetic K) (w : Word K) (ordinary alpha0 rho : K)
    (opened : Fin 22 → K) : K :=
  injectClaim ops (ops.evaluate7 (compact ops.toArithmetic ordinary (response w 0)) alpha0)
    rho opened

/-- Three later source compact rounds, on the same submitted word. -/
def terminalClaim (ops : Arithmetic K) (w : Word K) (coins : Fin 3 → K) (c : K) : K :=
  let c1 := ops.evaluate7 (compact ops.toArithmetic c (response w 1)) (coins 0)
  let c2 := ops.evaluate7 (compact ops.toArithmetic c1 (response w 2)) (coins 1)
  ops.evaluate7 (compact ops.toArithmetic c2 (response w 3)) (coins 2)

theorem produced_after_query (ops : Arithmetic K) (early : Fin 417 → K)
    (strategy : Strategy K Schedule) (tau alpha0 rho ordinary : K)
    (queries : Schedule) (coins : Fin 3 → K) (opened : Fin 22 → K) :
    afterQuery ops (produce early strategy tau alpha0 queries rho coins)
      ordinary alpha0 rho opened =
    ops.add (ops.evaluate7 (compact ops.toArithmetic ordinary (strategy tau).response0) alpha0)
      (increment ops rho opened) := by
  generalize h : (((strategy tau).afterAlpha0 alpha0).afterQueries queries rho) = tail
  cases tail with
  | round m1 n1 =>
    generalize h1 : n1 (coins 0) = t1
    cases t1 with
    | round m2 n2 =>
      generalize h2 : n2 (coins 1) = t2
      cases t2 with
      | round m3 n3 =>
        simp [afterQuery, injectClaim, produce, assembled_responses, roundsOfTail, h, h1, h2]

/-- Joins literal later field reads to the causal reply tree. It does not
assume any terminal equality, program coherence, or successful extraction. -/
theorem produced_terminal (ops : Arithmetic K) (early : Fin 417 → K)
    (strategy : Strategy K Schedule) (tau alpha0 rho : K) (queries : Schedule)
    (coins : Fin 3 → K) (c : K) :
    terminalClaim ops (produce early strategy tau alpha0 queries rho coins) coins c =
      tailClaim ops.toArithmetic
        (((strategy tau).afterAlpha0 alpha0).afterQueries queries rho) coins c := by
  generalize h : (((strategy tau).afterAlpha0 alpha0).afterQueries queries rho) = tail
  cases tail with
  | round m1 n1 =>
    generalize h1 : n1 (coins 0) = t1
    cases t1 with
    | round m2 n2 =>
      generalize h2 : n2 (coins 1) = t2
      cases t2 with
      | round m3 n3 =>
        have h3 : n3 (coins 2) = Tail.done := by cases n3 (coins 2); rfl
        simp [terminalClaim, produce, assembled_responses, roundsOfTail, h, h1, h2,
          h3, tailClaim, show (3 : Fin 4).val = 3 from rfl]

#print axioms produced_after_query
#print axioms produced_terminal
end AspisV8Completion.SameBodyQueryClaim
