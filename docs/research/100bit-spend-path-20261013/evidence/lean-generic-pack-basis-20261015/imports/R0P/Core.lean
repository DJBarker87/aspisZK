import Mathlib.Tactic

/-! # R0 semantic relation: shared skeleton for the per-family ports

The semantic terminal of the pinned source (`pair_forest_semantic_terminal.rs`)
evaluates residual lanes at an extension point.  On a Boolean row `b` its
row selectors are the indicators `[k = b]` and its openings are the trace
cells at `b`, `succ b` and `xor12 b`.  The **unrandomized relation** of a
family is: every residual it emits vanishes at every Boolean row.

Each family file (`Poseidon`, `Schedule`, `Path`, `Value`, `Occupancy`,
`Digest`, `Asset`, `Positive`, `Copy`) ports its source function literally as
a `Family K`, citing source line ranges, and proves row-local lemmas.  The
extraction implication (Part C) is stated over `Holds`. -/
set_option autoImplicit false
namespace R0P

/-- Physical trace: 29 columns (0–15 semantic C1, 16–25 mask-only C1,
26 = H1, 27 = G, 28 = D) over 1024 rows. -/
abbrev Trace (K : Type) := Fin 29 → Fin 1024 → K

/-- Big-endian row bits: coordinate `i` of row `b` is bit `9 - i`.  On
Boolean points the source's `succ` is increment mod 1024 and `xor12` flips
coordinates 6 and 7, i.e. `b xor 12`. -/
def succRow (b : Fin 1024) : Fin 1024 := ⟨(b.val + 1) % 1024, Nat.mod_lt _ (by norm_num)⟩
def xor12Row (b : Fin 1024) : Fin 1024 := ⟨b.val ^^^ 12, by
  have := b.isLt
  exact Nat.xor_lt_two_pow (n := 10) (by simpa using this) (by norm_num)⟩

/-- The three openings the terminal reads (16 semantic columns each). -/
structure Openings (K : Type) where
  z : Fin 16 → K
  succ : Fin 16 → K
  xor12 : Fin 16 → K

/-- Row selectors: `row k` of the source. -/
abbrev Sel (K : Type) := Fin 1024 → K

variable {K : Type} [Field K]

def rowOpenings (A : Trace K) (b : Fin 1024) : Openings K :=
  ⟨fun c => A (Fin.castLE (by norm_num) c) b, fun c => A (Fin.castLE (by norm_num) c) (succRow b),
    fun c => A (Fin.castLE (by norm_num) c) (xor12Row b)⟩

def rowSel (b : Fin 1024) : Sel K := fun k => if k = b then 1 else 0

/-- Digests are eight base-field elements, embedded in `K`. -/
abbrev Digest (K : Type) := Fin 8 → K

inductive Variant
  | privateTransfer
  | withdrawal
  deriving DecidableEq

/-- Port of `SemanticPublic` (terminal source lines 86–98), digests in `K`. -/
structure Public (K : Type) where
  variant : Variant
  anchor : Digest K
  nullifier : Digest K
  assetId : K
  recipient : Option (Digest K)
  change : Digest K
  withdrawalAmount : Option K
  nextPairIndex : Nat
  snapshotFrontier : Fin 20 → Digest K
  nextRoot : Digest K
  nextFrontier : Fin 20 → Digest K

/-- A residual family: a literal port of one source function. -/
structure Family (K : Type) where
  residuals : Public K → Openings K → Sel K → List K

/-- The family's unrandomized relation on a trace. -/
def Holds (f : Family K) (pub : Public K) (A : Trace K) : Prop :=
  ∀ b : Fin 1024, ∀ r ∈ f.residuals pub (rowOpenings A b) (rowSel b), r = 0

theorem rowSel_self (b : Fin 1024) : rowSel (K := K) b b = 1 := by simp [rowSel]

theorem rowSel_ne (b k : Fin 1024) (h : k ≠ b) : rowSel (K := K) b k = 0 := by simp [rowSel, h]

end R0P
