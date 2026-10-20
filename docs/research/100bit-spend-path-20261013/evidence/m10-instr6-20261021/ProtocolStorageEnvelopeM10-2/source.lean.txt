import RRReachableStorageM10
import FiniteCandidateMergeWorkM10

/-! Stored slots, not semantic degree, bound copy/heap reservations. Dense
matrix and complete basis storage, reachable padded RR rows and all merge
prefixes are covered. Generic finite-cardinality arguments avoid concrete
matrix, candidate or field enumeration. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.ProtocolStorageEnvelopeM10
open RRConcreteState RRReachableStorageM10
variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K]

def rowSlots (s : RawState K) : Nat := (s.rows.map List.length).sum+s.rows.length+1

theorem rows (D : Nat) (s : RawState K) (h : BoundedRows D s) :
    rowSlots s ≤ (D+2)^2 := by
  have hh := RawExtractorCostLedger.sum_charge_le s.rows List.length (D+1) (D+1) h.2.1 h.2.2
  have hl := h.2.1
  unfold rowSlots
  nlinarith

theorem reachable_rows (ell D d : Nat) (s : RawState K) (h : BoundedRows D s)
    {n : Nat} {u : RawState K} (hr : Reachable ell s n u) (hn : n ≤ d) :
    rowSlots u ≤ (D+(d+1)*(ell+1)+2)^2 := by
  have hu := reachable_bound ell D s h hr
  have hh := rows _ u hu
  have hm := Nat.mul_le_mul_right (ell+1) (show n ≤ d+1 by omega)
  exact hh.trans (Nat.pow_le_pow_left (by omega) 2)

theorem dense (R C : Nat) : R*C+R+C+1+C*C ≤ 3*(R+C+1)^2 := by
  let S := R+C+1
  have hr : R ≤ S := by unfold S; omega
  have hc : C ≤ S := by unfold S; omega
  have hp := Nat.mul_le_mul hr hc
  have hb := Nat.mul_le_mul hc hc
  have hs : S ≤ S*S := Nat.le_mul_of_pos_right _ (by unfold S; omega)
  change R*C+R+C+1+C*C ≤ 3*S^2
  rw [pow_two]
  have he : R+C+1 = S := rfl
  omega

variable {I M : Type} [Fintype I] [DecidableEq I] [DecidableEq M]

theorem merge_prefix (Ckeep Ceq B F : Nat) (keep : Finset I → (I → M) → Bool)
    (decoded : I → List M) (S : Finset I) (family : List (I → M)) (lanes : List I)
    (hF : family.length ≤ F) (hB : ∀ i, (decoded i).length ≤ B) :
    (FiniteCandidateMergeWorkM10.run Ckeep Ceq keep decoded S family lanes).1.length ≤ F*B^lanes.length := by
  induction lanes generalizing F S family with
  | nil => simpa only [FiniteCandidateMergeWorkM10.run,List.length_nil,pow_zero,Nat.mul_one] using hF
  | cons lane rest ih =>
    have ha := (FiniteCandidateMergeWorkM10.advance_length Ckeep Ceq keep S lane family (decoded lane)).trans
      (Nat.mul_le_mul hF (hB lane))
    have hh := ih (F*B) (insert lane S)
      (FiniteCandidateMergeWorkM10.advance Ckeep Ceq keep S lane family (decoded lane)).1 ha
    simpa only [FiniteCandidateMergeWorkM10.run,List.length_cons,pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hh

theorem merge_29 (Ckeep Ceq B : Nat) (keep : Finset (Fin 29) → (Fin 29 → M) → Bool)
    (decoded : Fin 29 → List M) (zero : Fin 29 → M) (lanes : List (Fin 29))
    (hB : ∀ i, (decoded i).length ≤ B) (hn : lanes.length ≤ 29) :
    (FiniteCandidateMergeWorkM10.run Ckeep Ceq keep decoded ∅ [zero] lanes).1.length ≤ (B+1)^29 := by
  have hh := merge_prefix Ckeep Ceq B 1 keep decoded ∅ [zero] lanes (by simp) hB
  simp only [Nat.one_mul] at hh
  exact hh.trans ((Nat.pow_le_pow_left (show B ≤ B+1 by omega) _).trans
    (Nat.pow_le_pow_right (show 1 ≤ B+1 by omega) hn))

#print axioms rows
#print axioms reachable_rows
#print axioms dense
#print axioms merge_prefix
#print axioms merge_29
end AspisR1.ProtocolStorageEnvelopeM10
end
