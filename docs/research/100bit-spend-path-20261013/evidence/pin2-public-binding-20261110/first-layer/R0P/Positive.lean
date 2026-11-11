import R0P.Core

/-! G1, pinned ebe7cbcdc315cde4f483f47a79262b8010984e98.
Source P = docs/research/v8-no-work-100-20260907/experiments/positive_transfer.rs.
This research-only adapter is explicitly selected by the lead's Q1; it is not
asserted to be enabled by a production feature. No packing or extraction claim. -/
set_option autoImplicit false
namespace R0P
variable {K : Type} [Field K]

/-- P:10–12,64–66: ROW=1014, COL=3, LANE=94; preserve multiplication order. -/
def positiveResidual (claims : Fin 84 → K) : K :=
  claims 1 * claims (28 + 1) * claims 3 - 1

/-- P:67–70: selector's ten ordered multiply steps, starting at ONE.
The Nat shift/and reads the literal ROW bits in the source's order. -/
def positiveSelector (z : Fin 10 → K) : K :=
  (List.ofFn (fun j : Fin 10 =>
    if ((1014 >>> (9-j.val)) &&& 1) = 1 then z j else 1-z j)).foldl (· * ·) 1

/-- Source terminal:28–34,1185–1191, P:64–66: three blocks of 28
selected claims. At Boolean rows these are the trace's three Core openings. -/
def positiveRowClaims (A : Trace K) (b : Fin 1024) (i : Fin 84) : K :=
  A ⟨i.val % 28, lt_trans (Nat.mod_lt _ (by omega)) (by omega)⟩
    (if i.val / 28 = 0 then b else if i.val / 28 = 1 then succRow b else xor12Row b)

/-- P:64–70,78: row-selector-weighted residual, before extension packing.
The selector product at a Boolean row is Core's row selector at ROW=1014. -/
def positiveFamily : Family K where
  residuals := fun _ o sel => [sel 1014 * (o.z 1 * o.succ 1 * o.z 3 - 1)]

theorem positive_claim_indices (A : Trace K) (b : Fin 1024) :
    positiveResidual (positiveRowClaims A b) =
      A 1 b * A 1 (succRow b) * A 3 b - 1 := by
  rfl

theorem positive_family_row_claims (pub : Public K) (A : Trace K) (b : Fin 1024) :
    positiveFamily.residuals pub (rowOpenings A b) (rowSel b) =
      [rowSel b 1014 * positiveResidual (positiveRowClaims A b)] := by
  rw [positive_claim_indices]
  rfl

theorem positive_holds_iff (pub : Public K) (A : Trace K) :
    Holds positiveFamily pub A ↔ A 1 1014 * A 1 1015 * A 3 1014 = 1 := by
  constructor
  · intro h
    have hrow := h 1014 (rowSel (K := K) 1014 1014 *
      ((rowOpenings A 1014).z 1 * (rowOpenings A 1014).succ 1 *
        (rowOpenings A 1014).z 3 - 1)) (by simp [positiveFamily])
    simpa [rowSel_self, rowOpenings, succRow, sub_eq_zero] using hrow
  · intro h b r hr
    simp only [positiveFamily, List.mem_singleton] at hr
    subst r
    by_cases hb : (1014 : Fin 1024) = b
    · subst b
      simpa [rowSel_self, rowOpenings, succRow, sub_eq_zero] using h
    · rw [rowSel_ne b 1014 hb, zero_mul]

#print axioms positive_claim_indices
#print axioms positive_family_row_claims
#print axioms positive_holds_iff
end R0P
