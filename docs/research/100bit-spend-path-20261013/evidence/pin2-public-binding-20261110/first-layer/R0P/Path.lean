import R0P.Core

/-! G2, source revision e4d68a70d3f6beb215c9f6dd418f4a2a3740c809.
T = crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs.
C = crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs.
Only the Boolean-row restriction of C's high/low selectors is represented by
Core.Sel. The marginal adapter below proves that restriction symbolically;
no off-domain equivalence of arbitrary selector inputs is claimed. -/
set_option autoImplicit false
namespace R0P
variable {K : Type} [Field K]

/-- C:138–176: address of a high-six-bit / low-four-bit selector pair. -/
def g2Row (h : Fin 64) (l : Fin 16) : Fin 1024 :=
  ⟨16*h.val+l.val, by omega⟩

/-- C:138–176, Boolean-row adapter for the high selector. -/
def g2High (sel : Sel K) (h : Fin 64) : K := ∑ l : Fin 16, sel (g2Row h l)

/-- C:138–176, Boolean-row adapter for the low selector. -/
def g2Low (sel : Sel K) (l : Fin 16) : K := ∑ h : Fin 64, sel (g2Row h l)

/-- T:156–164: literal left-to-right sum_high loop on one bounded range. -/
def g2SumHigh (sel : Sel K) (start count : Nat) (bound : start+count ≤ 64) : K :=
  (List.ofFn (fun i : Fin count => g2High sel ⟨start+i.val, by omega⟩)).foldl (· + ·) 0

theorem g2_fold_add (xs : List K) (a : K) : xs.foldl (· + ·) a = a + xs.sum := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih => simp only [List.foldl_cons, List.sum_cons, ih, add_assoc]

theorem g2_high_row (b : Fin 1024) (h : Fin 64) :
    g2High (rowSel (K := K) b) h = if h.val = b.val / 16 then 1 else 0 := by
  unfold g2High
  by_cases hh : h.val = b.val / 16
  · rw [if_pos hh]
    let l : Fin 16 := ⟨b.val % 16, Nat.mod_lt _ (by omega)⟩
    have he : g2Row h l = b := by apply Fin.ext; dsimp [g2Row, l]; omega
    rw [Finset.sum_eq_single l]
    · rw [he, rowSel_self]
    · intro k _ hk
      apply rowSel_ne
      intro heq
      have hv := congrArg Fin.val heq
      have hl : k = l := by apply Fin.ext; dsimp [g2Row, l] at *; omega
      exact hk hl
    · simp
  · rw [if_neg hh]
    apply Finset.sum_eq_zero
    intro l _
    apply rowSel_ne
    intro heq
    have hv := congrArg Fin.val heq
    apply hh
    dsimp [g2Row] at hv
    omega

theorem g2_low_row (b : Fin 1024) (l : Fin 16) :
    g2Low (rowSel (K := K) b) l = if l.val = b.val % 16 then 1 else 0 := by
  unfold g2Low
  by_cases hl : l.val = b.val % 16
  · rw [if_pos hl]
    let h : Fin 64 := ⟨b.val / 16, by omega⟩
    have he : g2Row h l = b := by apply Fin.ext; dsimp [g2Row, h]; omega
    rw [Finset.sum_eq_single h]
    · rw [he, rowSel_self]
    · intro k _ hk
      apply rowSel_ne
      intro heq
      have hv := congrArg Fin.val heq
      have hh : k = h := by apply Fin.ext; dsimp [g2Row, h] at *; omega
      exact hk hh
    · simp
  · rw [if_neg hl]
    apply Finset.sum_eq_zero
    intro h _
    apply rowSel_ne
    intro heq
    have hv := congrArg Fin.val heq
    apply hl
    dsimp [g2Row] at hv
    omega

theorem g2_sum_high_row (b : Fin 1024) (start count : Nat) (bound : start+count ≤ 64) :
    g2SumHigh (rowSel (K := K) b) start count bound =
      if start ≤ b.val/16 ∧ b.val/16 < start+count then 1 else 0 := by
  rw [g2SumHigh, g2_fold_add, zero_add, List.sum_ofFn]
  simp_rw [g2_high_row]
  by_cases hb : start ≤ b.val/16 ∧ b.val/16 < start+count
  · rw [if_pos hb]
    let k : Fin count := ⟨b.val/16-start, by omega⟩
    rw [Finset.sum_eq_single k]
    · simp only [k]; rw [if_pos (by omega)]
    · intro i _ hi
      rw [if_neg]
      intro he
      apply hi
      apply Fin.ext
      dsimp [k]
      omega
    · simp
  · rw [if_neg hb]
    apply Finset.sum_eq_zero
    intro i _
    rw [if_neg]
    intro he
    apply hb
    have := i.isLt
    omega

/-- T:399–404: sum_high(57..63) multiplied by the four low selectors,
with the source's left-associated addition and multiplication unchanged. -/
def pathSelector (sel : Sel K) : K :=
  g2SumHigh sel 57 6 (by omega) *
    (((g2Low sel 1 + g2Low sel 5) + g2Low sel 9) + g2Low sel 13)

/-- T:413–427: production path_lanes_literal, scalar slots 32–48. -/
def pathLanes (q : K) (o : Openings K) : List K :=
  let bit := o.z 0
  [q * (bit * (bit-1))] ++
  List.ofFn (fun i : Fin 8 => q * (1-bit) * (o.succ (i.castAdd 8)-o.z (i.addNat 1 |>.castLE (by omega)))) ++
  List.ofFn (fun i : Fin 8 => q * bit * (o.succ (i.natAdd 8)-o.z (i.addNat 1 |>.castLE (by omega))))

/-- T:394–409, production non-semantic-factor-audit branch. -/
def pathFamily : Family K where
  residuals := fun _ o sel => pathLanes (pathSelector sel) o

/-- T:399–404: the six path blocks, local rows 1,5,9,13. -/
abbrev PathRow (b : Fin 1024) : Prop :=
  57 ≤ b.val/16 ∧ b.val/16 < 63 ∧
    (b.val%16 = 1 ∨ b.val%16 = 5 ∨ b.val%16 = 9 ∨ b.val%16 = 13)

theorem path_selector_row (b : Fin 1024) :
    pathSelector (rowSel (K := K) b) = if PathRow b then 1 else 0 := by
  simp only [pathSelector, g2_sum_high_row, g2_low_row, PathRow]
  split_ifs <;> simp_all <;> omega

theorem path_holds_iff (pub : Public K) (A : Trace K) :
    Holds pathFamily pub A ↔ ∀ b : Fin 1024, PathRow b →
      A 0 b * (A 0 b-1) = 0 ∧
      (∀ i : Fin 8, (1-A 0 b) * (A (i.castAdd 21) (succRow b)-A (i.addNat 1 |>.castLE (by omega)) b) = 0) ∧
      (∀ i : Fin 8, A 0 b * (A (i.natAdd 8 |>.castLE (by omega)) (succRow b)-A (i.addNat 1 |>.castLE (by omega)) b) = 0) := by
  change (∀ b, ∀ r ∈ pathLanes (pathSelector (rowSel b)) (rowOpenings A b), r = 0) ↔ _
  simp only [pathLanes, List.forall_mem_append, List.forall_mem_cons,
    List.not_mem_nil, false_implies, implies_true, and_true, List.forall_mem_ofFn_iff]
  constructor
  · intro h b hb
    have := h b
    rw [path_selector_row, if_pos hb] at this
    simp only [one_mul, rowOpenings, and_assoc] at this
    convert this using 1 <;> rfl
  · intro h b
    rw [path_selector_row]
    by_cases hb : PathRow b
    · rw [if_pos hb]
      have hh := h b hb
      simp only [one_mul, rowOpenings, and_assoc]
      convert hh using 1 <;> rfl
    · rw [if_neg hb]
      simp only [zero_mul, implies_true, and_self]

#print axioms g2_fold_add
#print axioms g2_high_row
#print axioms g2_low_row
#print axioms g2_sum_high_row
#print axioms path_selector_row
#print axioms path_holds_iff
end R0P
