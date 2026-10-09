import SelectedSemanticCallbackGap

/-! Canonical big-endian restriction trace of one fixed 1,024-row table.

Round `r` multiplies the equality factors for coordinates strictly before
`r`, leaves coordinate `r` as a linear polynomial, and sums over every
Boolean row.  Thus its message depends only on the table and the already-seen
point prefix.  No endpoint equation is stored in a structure field: the final
equality with `tableMLEValue` is proved below.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
namespace AspisV8Completion.CanonicalTableReferenceTrace
open scoped BigOperators
open Polynomial
open AspisV6TranscriptRelationGrammar
open AspisV6AcceptedPathObligations
open AspisV8.SelectedCompactSemanticRepair
open AspisV8.SelectedSemanticLaneAggregation
open AspisV8Completion.SameBodySelectedSemanticSource

variable {K : Type*} [Field K] [DecidableEq K]

def pointFactor (point : Fin 10 → K) (row : Fin 1024) (coordinate : Fin 10) : K :=
  if bigEndianBit row coordinate then point coordinate else 1 - point coordinate

/-- Product of the first `n` big-endian equality factors.  Values past ten
are totalized by multiplication by one but are never used by the trace. -/
def prefixWeight (point : Fin 10 → K) (row : Fin 1024) : Nat → K
  | 0 => 1
  | n + 1 => prefixWeight point row n *
      if h : n < 10 then pointFactor point row ⟨n, h⟩ else 1

@[simp] theorem prefixWeight_succ (point : Fin 10 → K) (row : Fin 1024)
    (n : Nat) (h : n < 10) :
    prefixWeight point row (n + 1) =
      prefixWeight point row n * pointFactor point row ⟨n, h⟩ := by
  simp [prefixWeight, h]

theorem prefixWeight_eq_of_prefix (left right : Fin 10 → K)
    (row : Fin 1024) (n : Nat) (bounded : n ≤ 10)
    (same : ∀ coordinate, coordinate.val < n → left coordinate = right coordinate) :
    prefixWeight left row n = prefixWeight right row n := by
  induction n generalizing left right with
  | zero => rfl
  | succ n ih =>
      have hn : n < 10 := by omega
      rw [prefixWeight_succ left row n hn, prefixWeight_succ right row n hn]
      have earlier : prefixWeight left row n = prefixWeight right row n :=
        ih (left := left) (right := right) (by omega)
          (fun coordinate before => same coordinate (by omega))
      rw [earlier]
      congr 1
      unfold pointFactor
      have current : left ⟨n, hn⟩ = right ⟨n, hn⟩ := same ⟨n, hn⟩ (by
        show n < n + 1
        omega)
      by_cases bit : bigEndianBit row (⟨n, hn⟩ : Fin 10) <;>
        simp [bit, current]

noncomputable def bitPolynomial (row : Fin 1024) (coordinate : Fin 10) : K[X] :=
  if bigEndianBit row coordinate then X else 1 - X

@[simp] theorem eval_bitPolynomial (row : Fin 1024) (coordinate : Fin 10) (x : K) :
    (bitPolynomial row coordinate).eval x =
      if bigEndianBit row coordinate then x else 1 - x := by
  by_cases bit : bigEndianBit row coordinate <;> simp [bitPolynomial, bit]

/-- Honest univariate restriction sent before challenge `round`. -/
noncomputable def restrictionMessage (table : Fin 1024 → K)
    (point : Fin 10 → K) (round : Fin 10) : K[X] :=
  ∑ row, C (prefixWeight point row round.val * table row) * bitPolynomial row round

/-- Extensional causal statement: changing the current or future challenges
cannot change the message already fixed at this round. -/
theorem restrictionMessage_prefix_independent (table : Fin 1024 → K)
    (left right : Fin 10 → K) (round : Fin 10)
    (same : ∀ coordinate, coordinate.val < round.val →
      left coordinate = right coordinate) :
    restrictionMessage table left round = restrictionMessage table right round := by
  unfold restrictionMessage
  apply Finset.sum_congr rfl
  intro row _
  rw [prefixWeight_eq_of_prefix left right row round.val (by omega) same]

theorem restrictionMessage_degree (table : Fin 1024 → K)
    (point : Fin 10 → K) (round : Fin 10) :
    (restrictionMessage table point round).natDegree ≤ 27 := by
  unfold restrictionMessage
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro row _
  calc
    (C (prefixWeight point row round.val * table row) *
        bitPolynomial row round).natDegree ≤
        (bitPolynomial row round).natDegree := natDegree_C_mul_le _ _
    _ ≤ 27 := by
      by_cases bit : bigEndianBit row round
      · simp [bitPolynomial, bit]
      · rw [bitPolynomial, if_neg bit]
        exact (natDegree_sub_le 1 X).trans (by simp)

noncomputable def prefixClaim (table : Fin 1024 → K)
    (point : Fin 10 → K) (n : Nat) : K :=
  ∑ row, prefixWeight point row n * table row

theorem restrictionMessage_boundary (table : Fin 1024 → K)
    (point : Fin 10 → K) (round : Fin 10) :
    (restrictionMessage table point round).eval 0 +
      (restrictionMessage table point round).eval 1 =
        prefixClaim table point round.val := by
  simp only [restrictionMessage, Polynomial.eval_finsetSum, prefixClaim,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro row _
  by_cases bit : bigEndianBit row round <;>
    simp [bitPolynomial, bit]

theorem restrictionMessage_eval (table : Fin 1024 → K)
    (point : Fin 10 → K) (round : Fin 10) :
    (restrictionMessage table point round).eval (point round) =
      prefixClaim table point (round.val + 1) := by
  simp only [restrictionMessage, Polynomial.eval_finsetSum, prefixClaim]
  apply Finset.sum_congr rfl
  intro row _
  rw [prefixWeight_succ point row round.val round.isLt]
  by_cases bit : bigEndianBit row round <;>
    simp [bitPolynomial, pointFactor, bit] <;> ring

theorem prefixClaim_zero (table : Fin 1024 → K) (point : Fin 10 → K) :
    prefixClaim table point 0 = ∑ row, table row := by
  simp [prefixClaim, prefixWeight]

/-- Genuine table-derived trace.  The message at round `r` contains point
coordinates `0..r-1` only; the current coordinate remains the polynomial
variable. -/
noncomputable def canonicalReferenceTrace (table : Fin 1024 → K)
    (point : Fin 10 → K) : ReferenceTrace table point where
  messages := restrictionMessage table point
  degree := restrictionMessage_degree table point
  boundary := by
    intro round
    rw [restrictionMessage_boundary]
    by_cases first : round.val = 0
    · have roundZero : round = 0 := Fin.ext first
      subst round
      simpa [referenceClaim] using prefixClaim_zero table point
    · let previous : Fin 10 := ⟨round.val - 1, by omega⟩
      have successor : previous.succ = round.castSucc := by
        apply Fin.ext
        simp [previous]
        omega
      have previousNext : previous.val + 1 = round.val := by
        simp [previous]
        omega
      rw [← successor, referenceClaim]
      rw [← previousNext]
      exact (restrictionMessage_eval table point previous).symm

theorem prefixWeight_eq_prod (point : Fin 10 → K) (row : Fin 1024)
    (n : Nat) (bounded : n ≤ 10) :
    prefixWeight point row n =
      ∏ coordinate : Fin n,
        pointFactor point row ⟨coordinate.val, lt_of_lt_of_le coordinate.isLt bounded⟩ := by
  induction n with
  | zero => simp [prefixWeight]
  | succ n ih =>
      have hn : n < 10 := by omega
      rw [prefixWeight_succ point row n hn, Fin.prod_univ_castSucc]
      rw [ih (by omega)]
      congr 1

theorem prefixWeight_ten_eq_mleRowWeight
    (point : Fin 10 → K) (row : Fin 1024) :
    prefixWeight point row 10 = mleRowWeight point row := by
  rw [prefixWeight_eq_prod point row 10 (by omega)]
  unfold mleRowWeight pointFactor
  rfl

theorem prefixClaim_ten_eq_tableMLEValue
    (table : Fin 1024 → K) (point : Fin 10 → K) :
    prefixClaim table point 10 = tableMLEValue point table := by
  unfold prefixClaim tableMLEValue
  apply Finset.sum_congr rfl
  intro row _
  rw [prefixWeight_ten_eq_mleRowWeight]

/-- The canonical trace endpoint is proved, not postulated, to be the frozen
selected table's big-endian multilinear evaluation. -/
theorem canonicalReferenceTrace_terminal
    (table : Fin 1024 → K) (point : Fin 10 → K) :
    referenceClaim (∑ row, table row) (canonicalReferenceTrace table point).messages
      point (Fin.last 10) = tableMLEValue point table := by
  rw [referenceClaim]
  change (restrictionMessage table point (9 : Fin 10)).eval (point 9) = _
  rw [restrictionMessage_eval]
  simpa using prefixClaim_ten_eq_tableMLEValue table point

/-- The callback bridge specialized to the honest table-derived trace.  Its
only semantic premise is now the literal selected callback/table equality;
the trace endpoint is discharged by `canonicalReferenceTrace_terminal`. -/
theorem callback_exact_of_canonical_table
    (callback : SelectedTerminalCallback K) (fields : FixedFieldView K)
    (point : Fin 10 → K) (table : Fin 1024 → K)
    (callbackReturnsTable : callback (terminalProjection fields.pointClaim) point =
      some (SelectedSemanticCallbackGap.fixedTableTerminal table point)) :
    callback (terminalProjection fields.pointClaim) point = some
      (referenceClaim (∑ row, table row) (canonicalReferenceTrace table point).messages
        point (Fin.last 10)) := by
  apply SelectedSemanticCallbackGap.callback_exact_of_table_terminal
    callback fields point (canonicalReferenceTrace table point) callbackReturnsTable
  exact canonicalReferenceTrace_terminal table point

#print canonicalReferenceTrace_terminal
#print axioms restrictionMessage_prefix_independent
#print axioms restrictionMessage_degree
#print axioms restrictionMessage_boundary
#print axioms restrictionMessage_eval
#print axioms canonicalReferenceTrace
#print axioms canonicalReferenceTrace_terminal
#print axioms callback_exact_of_canonical_table
end AspisV8Completion.CanonicalTableReferenceTrace
