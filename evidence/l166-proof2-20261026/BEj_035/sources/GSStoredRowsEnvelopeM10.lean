import GSConcreteInterpolation
import RRRuntimeNormalizedChildReconstruction
import ExtractorWorkMonad

/-! Stored representation bounds for the actual GS row constructor and RR
normalization. The runtime row at slice n stores n+1 entries, even if the
represented polynomial has much smaller degree. No concrete rows are reduced. -/
set_option autoImplicit false
namespace AspisR1.GSStoredRowsEnvelopeM10
open GSRawStateCoefficientBridge
variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K]

def slots (rows : List (List K)) : Nat := (rows.map List.length).sum

theorem slots_bound (rows : List (List K)) (height width : Nat)
    (hh : rows.length ≤ height) (hw : ∀ row ∈ rows, row.length ≤ width) :
    slots rows ≤ height*width := by
  have hsum : (rows.map List.length).sum ≤ rows.length*width := by
    induction rows with
    | nil => simp
    | cons row rest ih =>
      have hr := hw row List.mem_cons_self
      have ht := ih (by simp only [List.length_cons] at hh; omega)
        (fun r hr => hw r (List.mem_cons_of_mem _ hr))
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega
  exact hsum.trans (Nat.mul_le_mul_right width hh)

theorem gsRows_length (Q : CompPoly.CBivariate K) (x y : Nat) :
    (gsRows Q x y).length = x+1 := List.length_ofFn

theorem gsRows_row_length (Q : CompPoly.CBivariate K) (x y : Nat)
    (row : List K) (h : row ∈ gsRows Q x y) : row.length = y+1 := by
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp h
  exact List.length_ofFn

theorem gsRows_slots (Q : CompPoly.CBivariate K) (x y : Nat) :
    slots (gsRows Q x y) ≤ (x+1)*(y+1) :=
  slots_bound _ _ _ (gsRows_length Q x y).le
    (fun r hr => (gsRows_row_length Q x y r hr).le)

theorem runtime_row_length (gs : List (List K)) (a : K) (M n : Nat) :
    (RRVectorRowPolynomialBridge.row gs a M n).length = n+1 := List.length_ofFn

theorem rowsThrough_length (gs : List (List K)) (a : K) (M B : Nat) :
    (RRVectorNormalizedRows.rowsThrough gs a M B).length = B+1 := List.length_ofFn

theorem rowsThrough_width (gs : List (List K)) (a : K) (M B : Nat)
    (row : List K) (hr : row ∈ RRVectorNormalizedRows.rowsThrough gs a M B) :
    row.length ≤ B+1 := by
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
  rw [runtime_row_length]
  have hi := i.isLt
  omega

theorem runtime_slots (gs : List (List K)) (a : K) (M ell v : Nat) :
    slots (RRRuntimeNormalizedChildReconstruction.runtimeRows gs a M ell v) ≤
      (M+ell+1)^2 := by
  rw [pow_two]
  apply slots_bound _ (M+ell+1) (M+ell+1)
  · simp only [RRRuntimeNormalizedChildReconstruction.runtimeRows, List.length_drop,
      rowsThrough_length]
    omega
  · intro row hr
    exact rowsThrough_width gs a M (M+ell) row (List.mem_of_mem_drop hr)

/-- One additional descent raises maxX by at most ell, regardless of the
normalizing shift. This pays for the representation rather than its degree. -/
theorem maxX_step (M ell v : Nat) : M+ell-v ≤ M+ell := Nat.sub_le _ _

/-- Every descent on a d-step branch stays within one public maxX cap.
The cap accounts the implemented M+ell-v update; it does not use degree to
assert a false stored-row-width invariant. -/
def maxXAfter (ell : Nat) : Nat → Nat → List Nat → Nat
  | 0, M, _ => M
  | _+1, M, [] => M
  | fuel+1, M, v::vs => maxXAfter ell fuel (M+ell-v) vs

theorem maxXAfter_bound (ell fuel M : Nat) (vs : List Nat) :
    maxXAfter ell fuel M vs ≤ M+fuel*ell := by
  induction fuel generalizing M vs with
  | zero => simp only [maxXAfter, Nat.zero_mul, Nat.add_zero, Nat.le_refl]
  | succ fuel ih =>
    cases vs with
    | nil => simp only [maxXAfter]; omega
    | cons v vs =>
      have h := ih (M+ell-v) vs
      simp only [maxXAfter, Nat.add_mul, Nat.one_mul]
      omega

/-- A fixed number of normalized states, including aborted prefixes, can
allocate at most their count times the maximum stored-row square. -/
theorem cumulative_row_bits (states D width : Nat) (alloc : Nat)
    (h : alloc ≤ states*(D+1)^2) : alloc*width ≤ states*(D+1)^2*width :=
  Nat.mul_le_mul_right width h

#print axioms slots_bound
#print axioms gsRows_length
#print axioms gsRows_row_length
#print axioms gsRows_slots
#print axioms runtime_row_length
#print axioms rowsThrough_length
#print axioms rowsThrough_width
#print axioms runtime_slots
#print axioms maxX_step
#print axioms maxXAfter_bound
#print axioms cumulative_row_bits
end AspisR1.GSStoredRowsEnvelopeM10
