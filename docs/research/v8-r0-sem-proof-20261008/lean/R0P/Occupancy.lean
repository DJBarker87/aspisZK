import R0P.Core

/-! G1, pinned ebe7cbcdc315cde4f483f47a79262b8010984e98.
Source T = crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs.
Port the literal production path, not occupancy_lanes_factored (T:580–605).
These are the 12 contributions added to scalar slots 0–11, before packing. -/
set_option autoImplicit false
namespace R0P
variable {K : Type} [Field K]

/-- T:521–527, variant_expected_output, with M31 literals cast to K. -/
def occupancyExpected (variant : Variant) : K :=
  match variant with | .privateTransfer => 1 | .withdrawal => 0

/-- T:556–578, occupancy_lanes_literal. List order is the array's lane order;
the eight digest lanes stay symbolically indexed. -/
def occupancyLanesLiteral (input output expected : K) (opened : Fin 16 → K) : List K :=
  let occupied := opened 0
  let inverse := opened 1
  let one_minus := 1 - occupied
  let both := input + output
  [both * (occupied * (occupied - 1)),
   both * (opened 9 * inverse - occupied),
   both * (one_minus * inverse)] ++
  List.ofFn (fun lane : Fin 8 => both * (one_minus * opened ⟨2+lane.val, by omega⟩)) ++
  [input * (opened 10 * one_minus) + output * (occupied - expected)]

/-- T:60–61,530–554: selectors at 63*16+9 and 63*16+10; production
cfg(not(feature="pool-v1-pair-forest-semantic-factor-audit")). -/
def occupancyFamily : Family K where
  residuals := fun pub o sel => occupancyLanesLiteral
    (sel (63*16+9)) (sel (63*16+10)) (occupancyExpected pub.variant) o.z

 theorem occupancy_lanes_zero_iff (input output expected : K) (o : Fin 16 → K) :
    (∀ r ∈ occupancyLanesLiteral input output expected o, r = 0) ↔
      (input+output) * (o 0 * (o 0-1)) = 0 ∧
      (input+output) * (o 9 * o 1-o 0) = 0 ∧
      (input+output) * ((1-o 0)*o 1) = 0 ∧
      (∀ lane : Fin 8, (input+output)*((1-o 0)*o ⟨2+lane.val, by omega⟩) = 0) ∧
      input*(o 10*(1-o 0)) + output*(o 0-expected) = 0 := by
  simp [occupancyLanesLiteral, List.forall_mem_ofFn_iff, and_assoc]

theorem occupancy_holds_iff (pub : Public K) (A : Trace K) :
    Holds occupancyFamily pub A ↔
      (∀ b : Fin 1024, b = 1017 ∨ b = 1018 →
        A 0 b * (A 0 b-1) = 0 ∧
        A 9 b * A 1 b-A 0 b = 0 ∧
        (1-A 0 b)*A 1 b = 0 ∧
        ∀ lane : Fin 8, (1-A 0 b)*A ⟨2+lane.val, by omega⟩ b = 0) ∧
      A 10 1017 * (1-A 0 1017) = 0 ∧
      A 0 1018 = (match pub.variant with | .privateTransfer => 1 | .withdrawal => 0) := by
  change (∀ b, ∀ r ∈ occupancyLanesLiteral (rowSel b 1017) (rowSel b 1018)
    (occupancyExpected pub.variant) (rowOpenings A b).z, r = 0) ↔ _
  simp_rw [occupancy_lanes_zero_iff]
  constructor
  · intro h
    have hi := h 1017
    have ho := h 1018
    simp [rowSel, rowOpenings] at hi ho
    refine ⟨?_, hi.2.2.2.2, ?_⟩
    · intro b hb
      rcases hb with rfl | rfl
      · exact ⟨hi.1, hi.2.1, hi.2.2.1, hi.2.2.2.1⟩
      · exact ⟨ho.1, ho.2.1, ho.2.2.1, ho.2.2.2.1⟩
    · simpa [occupancyExpected, sub_eq_zero] using ho.2.2.2.2
  · rintro ⟨hboth, hi, ho⟩ b
    by_cases hb : (1017 : Fin 1024) = b
    · subst b
      have h := hboth 1017 (Or.inl rfl)
      simpa [rowSel, rowOpenings] using
        And.intro h.1 (And.intro h.2.1 (And.intro h.2.2.1 (And.intro h.2.2.2 hi)))
    · by_cases hc : (1018 : Fin 1024) = b
      · subst b
        have h := hboth 1018 (Or.inr rfl)
        have hoe : A 0 1018 - occupancyExpected pub.variant = 0 := by
          simpa [occupancyExpected, sub_eq_zero] using ho
        simpa [rowSel, rowOpenings] using
          And.intro h.1 (And.intro h.2.1 (And.intro h.2.2.1 (And.intro h.2.2.2 hoe)))
      · rw [rowSel_ne b 1017 hb, rowSel_ne b 1018 hc]
        simp

#print axioms occupancy_lanes_zero_iff
#print axioms occupancy_holds_iff
end R0P
