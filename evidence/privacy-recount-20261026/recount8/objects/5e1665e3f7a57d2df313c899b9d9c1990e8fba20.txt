import Mathlib.Data.Fin.Basic
set_option autoImplicit false
namespace R1Z.PV_RunJoin_Prefix
variable {Raw : Type}
abbrev Tape (Raw : Type) := Fin 128 → Raw
/-- A context can inspect exactly the draws strictly before i. Its dependent
function argument has no address for the current or any future raw draw. -/
abbrev Prefix (Raw : Type) (i : Fin 128) := {j : Fin 128 // j.val < i.val} → Raw

def restrictTape (i : Fin 128) (t : Tape Raw) : Prefix Raw i := fun j => t j.val

theorem prefix_eq (i : Fin 128) (t u : Tape Raw)
    (same : ∀ j : Fin 128, j.val < i.val → t j = u j) :
    restrictTape i t = restrictTape i u := by
  funext j
  exact same j.val j.property

/-- The residual world may include all fixed prior public context, oracle
state, failure tags, files, time and worker replies. This construction does
not assert that the actual extracted producer factors through Prefix. -/
def frame {Rest Context : Type}
    (produce : (i : Fin 128) → Prefix Raw i → Rest → Context)
    (i : Fin 128) (c : Tape Raw × Rest) : Context := produce i (restrictTape i c.1) c.2

theorem causal {Rest Context : Type}
    (produce : (i : Fin 128) → Prefix Raw i → Rest → Context)
    (i : Fin 128) (t u : Tape Raw) (rest : Rest)
    (same : ∀ j : Fin 128, j.val < i.val → t j = u j) :
    frame produce i (t,rest) = frame produce i (u,rest) := by
  exact congrArg (fun p => produce i p rest) (prefix_eq i t u same)

/-- Fill only coordinates absent from the restrictTape with a fixed zero. This is
used to prove an equivalence, not to change any runtime's execution tape. -/
def extend [Zero Raw] (i : Fin 128) (p : Prefix Raw i) : Tape Raw :=
  fun j => if h : j.val < i.val then p ⟨j,h⟩ else 0

theorem extend_prefix [Zero Raw] (i : Fin 128) (t : Tape Raw)
    (j : Fin 128) (before : j.val < i.val) :
    extend i (restrictTape i t) j = t j := by
  simp only [extend,dif_pos before,restrictTape]

theorem prefix_extend [Zero Raw] (i : Fin 128) (p : Prefix Raw i) :
    restrictTape i (extend i p) = p := by
  funext j
  simp only [restrictTape,extend,dif_pos j.property]

/-- Causality is exactly factorization through the strict restrictTape. This can be
used to audit an existing frame without quietly replacing it by a new one. -/
theorem causal_iff_factor [Zero Raw] {Rest Context : Type}
    (original : Fin 128 → Tape Raw × Rest → Context) :
    (∀ (i : Fin 128) (t u : Tape Raw) (rest : Rest),
      (∀ j : Fin 128, j.val < i.val → t j = u j) →
        original i (t,rest) = original i (u,rest)) ↔
    (∀ (i : Fin 128) (t : Tape Raw) (rest : Rest),
      original i (t,rest) = original i (extend i (restrictTape i t),rest)) := by
  constructor
  · intro causal i t rest
    exact causal i t (extend i (restrictTape i t)) rest
      (fun j before => (extend_prefix i t j before).symm)
  · intro factor i t u rest same
    rw [factor i t rest,factor i u rest,prefix_eq i t u same]


#print axioms prefix_eq
#print axioms causal
#print axioms extend_prefix
#print axioms prefix_extend
#print axioms causal_iff_factor
end R1Z.PV_RunJoin_Prefix
