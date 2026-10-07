import R0P.Core

/-! G1, pinned ebe7cbcdc315cde4f483f47a79262b8010984e98.
Source T = crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs.
Production cfg(not(feature="pool-v1-pair-forest-packed-range-audit"));
35 contributions at scalar slots 49–83, before packing. The two padding
residuals at slots 80–81 are retained: bits plus reconstruction alone do not
imply this family's range constraints. See the G1 finding in LOG.md. -/
set_option autoImplicit false
namespace R0P
variable {K : Type} [Field K]

/-- T:167–173, reconstruct_10. The nine reverse fold iterations are
written in order, preserving acc.add(acc).add(bit) without simplification. -/
def valueReconstruct10 (view : Fin 16 → K) : K :=
  let acc := view 9
  let acc := acc + acc + view 8
  let acc := acc + acc + view 7
  let acc := acc + acc + view 6
  let acc := acc + acc + view 5
  let acc := acc + acc + view 4
  let acc := acc + acc + view 3
  let acc := acc + acc + view 2
  let acc := acc + acc + view 1
  let acc := acc + acc + view 0
  acc

/-- T:477–502, unweighted range array in literal lane order, including
both zero-padding cells. square is written as ^2, with subtraction unchanged. -/
def valueRange (o : Openings K) : List K :=
  List.ofFn (fun i : Fin 10 => (o.z (i.castAdd 6))^2 - o.z (i.castAdd 6)) ++
  List.ofFn (fun i : Fin 10 => (o.succ (i.castAdd 6))^2 - o.succ (i.castAdd 6)) ++
  List.ofFn (fun i : Fin 10 => (o.xor12 (i.castAdd 6))^2 - o.xor12 (i.castAdd 6)) ++
  [o.z 10 - ((valueReconstruct10 o.z + valueReconstruct10 o.succ * (1024 : K)) +
      valueReconstruct10 o.xor12 * (1048576 : K)), o.succ 10, o.xor12 10]

/-- T:59,466–519, add_value_lanes. The source's initial zero and left-to-right
selector addition are retained; map is the production weighting loop. -/
def valueFamily : Family K where
  residuals := fun _ o sel =>
    let valueSelectors : Fin 3 → K := ![sel (16*63+0), sel (16*63+2), sel (16*63+4)]
    let rangeSelector := ((0 + valueSelectors 0) + valueSelectors 1) + valueSelectors 2
    let conservationSelector := sel (16*63+6)
    (valueRange o).map (fun residual => rangeSelector * residual) ++
      [conservationSelector * ((o.z 0-o.z 1)-o.z 2),
       conservationSelector * (o.succ 0-o.succ 1)]

theorem value_reconstruct10_eq (view : Fin 16 → K) :
    valueReconstruct10 view = view 0 + 2 * view 1 + 4 * view 2 + 8 * view 3 + 16 * view 4 + 32 * view 5 + 64 * view 6 + 128 * view 7 + 256 * view 8 + 512 * view 9 := by
  dsimp only [valueReconstruct10]
  ring

theorem value_bit_iff (x : K) : x^2-x = 0 ↔ x = 0 ∨ x = 1 := by
  rw [show x^2-x = x*(x-1) by ring, mul_eq_zero, sub_eq_zero]

theorem value_range_zero_iff (o : Openings K) :
    (∀ r ∈ valueRange o, r = 0) ↔
      (∀ i : Fin 10, o.z (i.castAdd 6) = 0 ∨ o.z (i.castAdd 6) = 1) ∧
      (∀ i : Fin 10, o.succ (i.castAdd 6) = 0 ∨ o.succ (i.castAdd 6) = 1) ∧
      (∀ i : Fin 10, o.xor12 (i.castAdd 6) = 0 ∨ o.xor12 (i.castAdd 6) = 1) ∧
      o.z 10 = ((o.z 0 + 2 * o.z 1 + 4 * o.z 2 + 8 * o.z 3 + 16 * o.z 4 + 32 * o.z 5 + 64 * o.z 6 + 128 * o.z 7 + 256 * o.z 8 + 512 * o.z 9) +
        (o.succ 0 + 2 * o.succ 1 + 4 * o.succ 2 + 8 * o.succ 3 + 16 * o.succ 4 + 32 * o.succ 5 + 64 * o.succ 6 + 128 * o.succ 7 + 256 * o.succ 8 + 512 * o.succ 9) * 1024) +
        (o.xor12 0 + 2 * o.xor12 1 + 4 * o.xor12 2 + 8 * o.xor12 3 + 16 * o.xor12 4 + 32 * o.xor12 5 + 64 * o.xor12 6 + 128 * o.xor12 7 + 256 * o.xor12 8 + 512 * o.xor12 9) * 1048576 ∧
      o.succ 10 = 0 ∧ o.xor12 10 = 0 := by
  simp only [valueRange, List.forall_mem_append, List.forall_mem_ofFn_iff,
    List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
    and_true, and_assoc, value_bit_iff, value_reconstruct10_eq]
  simp only [sub_eq_zero]

theorem value_range_selector (b : Fin 1024) (hb : b = 1008 ∨ b = 1010 ∨ b = 1012) :
    ((0 + rowSel (K := K) b 1008) + rowSel b 1010) + rowSel b 1012 = 1 := by
  rcases hb with rfl | rfl | rfl <;> simp [rowSel]

theorem value_holds_rows_iff (pub : Public K) (A : Trace K) :
    Holds valueFamily pub A ↔
      (∀ b : Fin 1024, b = 1008 ∨ b = 1010 ∨ b = 1012 →
        ∀ r ∈ valueRange (rowOpenings A b), r = 0) ∧
      A 0 1014 = A 1 1014 + A 2 1014 ∧ A 0 1015 = A 1 1015 := by
  change (∀ b, ∀ r ∈
    (valueRange (rowOpenings A b)).map
      (fun r => (((0 + rowSel b 1008) + rowSel b 1010) + rowSel b 1012) * r) ++
    [rowSel b 1014 * (((rowOpenings A b).z 0-(rowOpenings A b).z 1)-(rowOpenings A b).z 2),
     rowSel b 1014 * ((rowOpenings A b).succ 0-(rowOpenings A b).succ 1)], r = 0) ↔ _
  simp only [List.forall_mem_append, List.forall_mem_map, List.forall_mem_cons,
    List.not_mem_nil, false_implies, implies_true, and_true]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro b hb
      simpa only [value_range_selector b hb, one_mul] using (h b).1
    · simpa [rowSel_self, rowOpenings, sub_sub, sub_eq_zero] using (h 1014).2.1
    · simpa [rowSel_self, rowOpenings, succRow, sub_eq_zero] using (h 1014).2.2
  · rintro ⟨hrange, hcon, hcopy⟩ b
    refine ⟨?_, ?_, ?_⟩
    · by_cases hb : b = 1008 ∨ b = 1010 ∨ b = 1012
      · simpa only [value_range_selector b hb, one_mul] using hrange b hb
      · have h0 : (1008 : Fin 1024) ≠ b := fun h => hb (Or.inl h.symm)
        have h1 : (1010 : Fin 1024) ≠ b := fun h => hb (Or.inr (Or.inl h.symm))
        have h2 : (1012 : Fin 1024) ≠ b := fun h => hb (Or.inr (Or.inr h.symm))
        rw [rowSel_ne b 1008 h0, rowSel_ne b 1010 h1, rowSel_ne b 1012 h2]
        simp only [zero_add, zero_mul, implies_true]
    · by_cases hb : (1014 : Fin 1024) = b
      · subst b
        simpa [rowSel_self, rowOpenings, sub_sub, sub_eq_zero] using hcon
      · rw [rowSel_ne b 1014 hb, zero_mul]
    · by_cases hb : (1014 : Fin 1024) = b
      · subst b
        simpa [rowSel_self, rowOpenings, succRow, sub_eq_zero] using hcopy
      · rw [rowSel_ne b 1014 hb, zero_mul]

/-- All range equations, with the source's two padding equations included.
G1(a) without the last two conjuncts is false; LOG.md supplies a counterexample. -/
theorem value_holds_iff (pub : Public K) (A : Trace K) :
    Holds valueFamily pub A ↔
      (∀ b : Fin 1024, b = 1008 ∨ b = 1010 ∨ b = 1012 →
      (∀ i : Fin 10, A (i.castAdd 19) b = 0 ∨ A (i.castAdd 19) b = 1) ∧
      (∀ i : Fin 10, A (i.castAdd 19) (succRow b) = 0 ∨ A (i.castAdd 19) (succRow b) = 1) ∧
      (∀ i : Fin 10, A (i.castAdd 19) (xor12Row b) = 0 ∨ A (i.castAdd 19) (xor12Row b) = 1) ∧
      A 10 b = ((A 0 b + 2 * A 1 b + 4 * A 2 b + 8 * A 3 b + 16 * A 4 b + 32 * A 5 b + 64 * A 6 b + 128 * A 7 b + 256 * A 8 b + 512 * A 9 b) +
        (A 0 (succRow b) + 2 * A 1 (succRow b) + 4 * A 2 (succRow b) + 8 * A 3 (succRow b) + 16 * A 4 (succRow b) + 32 * A 5 (succRow b) + 64 * A 6 (succRow b) + 128 * A 7 (succRow b) + 256 * A 8 (succRow b) + 512 * A 9 (succRow b)) * 1024) +
        (A 0 (xor12Row b) + 2 * A 1 (xor12Row b) + 4 * A 2 (xor12Row b) + 8 * A 3 (xor12Row b) + 16 * A 4 (xor12Row b) + 32 * A 5 (xor12Row b) + 64 * A 6 (xor12Row b) + 128 * A 7 (xor12Row b) + 256 * A 8 (xor12Row b) + 512 * A 9 (xor12Row b)) * 1048576 ∧
      A 10 (succRow b) = 0 ∧ A 10 (xor12Row b) = 0) ∧
      A 0 1014 = A 1 1014 + A 2 1014 ∧ A 0 1015 = A 1 1015 := by
  rw [value_holds_rows_iff]
  simp only [value_range_zero_iff, rowOpenings]
  rfl

#print axioms value_reconstruct10_eq
#print axioms value_bit_iff
#print axioms value_range_zero_iff
#print axioms value_range_selector
#print axioms value_holds_rows_iff
#print axioms value_holds_iff
end R0P
