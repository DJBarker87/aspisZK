import R1Z.PV_RunJoin_Prefix
import R1Z.PV_RunJoin_CompletedWorld
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CausalPrefix
local instance : ProverRwRngCaller.NativeTypes := PV_RunJoin_CallerWorld.nativeTypes

abbrev Raw := Fin 2 → R0Z.FsStatement.OracleAnswer
abbrev Tape := Fin 128 → Raw

/-- A context can inspect exactly the draws strictly before i. Its dependent
function argument has no address for the current or any future raw draw. -/
abbrev Prefix (i : Fin 128) := {j : Fin 128 // j.val < i.val} → Raw

def restrictTape (i : Fin 128) (t : Tape) : Prefix i := fun j => t j.val

theorem prefix_eq (i : Fin 128) (t u : Tape)
    (same : ∀ j : Fin 128, j.val < i.val → t j = u j) :
    restrictTape i t = restrictTape i u := by
  exact PV_RunJoin_Prefix.prefix_eq i t u same

/-- The residual world may include all fixed prior public context, oracle
state, failure tags, files, time and worker replies. This construction does
not assert that the actual extracted producer factors through Prefix. -/
def frame {Rest Context : Type}
    (produce : (i : Fin 128) → Prefix i → Rest → Context)
    (i : Fin 128) (c : Tape × Rest) : Context := produce i (restrictTape i c.1) c.2

theorem causal {Rest Context : Type}
    (produce : (i : Fin 128) → Prefix i → Rest → Context)
    (i : Fin 128) (t u : Tape) (rest : Rest)
    (same : ∀ j : Fin 128, j.val < i.val → t j = u j) :
    frame produce i (t,rest) = frame produce i (u,rest) := by
  exact PV_RunJoin_Prefix.causal produce i t u rest same

/-- Fill only coordinates absent from the restrictTape with a fixed zero. This is
used to prove an equivalence, not to change any runtime's execution tape. -/
def extend (i : Fin 128) (p : Prefix i) : Tape :=
  fun j => if h : j.val < i.val then p ⟨j,h⟩ else 0

theorem extend_prefix (i : Fin 128) (t : Tape)
    (j : Fin 128) (before : j.val < i.val) :
    extend i (restrictTape i t) j = t j := by
  exact PV_RunJoin_Prefix.extend_prefix i t j before

theorem prefix_extend (i : Fin 128) (p : Prefix i) :
    restrictTape i (extend i p) = p := by
  exact PV_RunJoin_Prefix.prefix_extend i p

/-- Causality is exactly factorization through the strict restrictTape. This can be
used to audit an existing frame without quietly replacing it by a new one. -/
theorem causal_iff_factor {Rest Context : Type}
    (original : Fin 128 → Tape × Rest → Context) :
    (∀ (i : Fin 128) (t u : Tape) (rest : Rest),
      (∀ j : Fin 128, j.val < i.val → t j = u j) →
        original i (t,rest) = original i (u,rest)) ↔
    (∀ (i : Fin 128) (t : Tape) (rest : Rest),
      original i (t,rest) = original i (extend i (restrictTape i t),rest)) := by
  exact PV_RunJoin_Prefix.causal_iff_factor original

/-- Construct the initialized world with the ledger taken from the residual
coordinate. Replies may retain error tags and partial writes. No availability,
uniformity or native/source interpretation is inferred from this data. -/
def world {Coins Rest N L C : Type}
    (coordinates : Coins ≃ Tape × Rest)
    (replies : Coins → Fin 128 →
      (Aeneas.Std.Array Aeneas.Std.U8 64#usize ×
        Aeneas.Std.core.result.Result Unit ProverRwRngCaller.getrandom.error.Error))
    (policy : Rest → N) (ledger : Rest → L)
    (body : Rest → C) :
    PV_RunJoin_CompletedWorld.Data Coins N L C where
  replies := replies
  policy := fun c => policy (coordinates c).2
  ledger := fun c => ledger (coordinates c).2
  body := fun c => body (coordinates c).2

theorem initial_ledger {Coins Rest N L C : Type}
    (coordinates : Coins ≃ Tape × Rest)
    (replies : Coins → Fin 128 →
      (Aeneas.Std.Array Aeneas.Std.U8 64#usize ×
        Aeneas.Std.core.result.Result Unit ProverRwRngCaller.getrandom.error.Error))
    (policy : Rest → N) (ledger : Rest → L)
    (body : Rest → C) (t u : Tape) (rest : Rest) :
    (world coordinates replies policy ledger body).ledger (coordinates.symm (t,rest)) =
      (world coordinates replies policy ledger body).ledger (coordinates.symm (u,rest)) := by
  change ledger (coordinates (coordinates.symm (t,rest))).2 =
    ledger (coordinates (coordinates.symm (u,rest))).2
  simp only [coordinates.apply_symm_apply]

#print axioms prefix_eq
#print axioms causal
#print axioms extend_prefix
#print axioms prefix_extend
#print axioms causal_iff_factor
#print axioms initial_ledger
end R1Z.PV_RunJoin_CausalPrefix
