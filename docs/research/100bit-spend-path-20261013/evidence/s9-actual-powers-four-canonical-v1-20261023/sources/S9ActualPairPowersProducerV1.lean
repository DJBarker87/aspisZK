import S9ActualPairPowersInvariantV1
import S9ActualPairWideCanonicalV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ActualPairPowersProducerV1
open AspisR1S9ActualPairWideCanonicalV1

private theorem zero_canonical : Canonical
    AspisR1S9ProductionPairCutV1.aspis_core.field.wide_exact.WideExact.ZERO := by
  simp only [AspisR1S9ProductionPairCutV1.aspis_core.field.wide_exact.WideExact.ZERO,
    AspisR1S9ProductionPairCutV1.aspis_core.field.QM31.ZERO]
  change ((0 < 2147483647 ∧ 0 < 2147483647) ∧
          (0 < 2147483647 ∧ 0 < 2147483647)) ∧
         ((0 < 2147483647 ∧ 0 < 2147483647) ∧
          (0 < 2147483647 ∧ 0 < 2147483647))
  decide

private theorem one_canonical : Canonical
    AspisR1S9ProductionPairCutV1.aspis_core.field.wide_exact.WideExact.ONE := by
  simp only [AspisR1S9ProductionPairCutV1.aspis_core.field.wide_exact.WideExact.ONE,
    AspisR1S9ProductionPairCutV1.aspis_core.field.QM31.ONE,
    AspisR1S9ProductionPairCutV1.aspis_core.field.QM31.ZERO]
  change ((1 < 2147483647 ∧ 0 < 2147483647) ∧
          (0 < 2147483647 ∧ 0 < 2147483647)) ∧
         ((0 < 2147483647 ∧ 0 < 2147483647) ∧
          (0 < 2147483647 ∧ 0 < 2147483647))
  decide

/-- Same-call producer theorem for the shipped indexed powers(4,alpha)
implementation. The only arithmetic input condition is canonical alpha;
canonical ZERO, ONE and every successful running-product result are proved.
The exact returned array has canonical CurrentWide-coordinate reads. -/
theorem actual_powers_four_success_canonical
    (x : W) (out : Array W 4#usize) (hx : Canonical x)
    (hrun : AspisR1S9ProductionPairCutV1.weights.powers 4#usize x = .ok out) :
    ∀ (i : Usize) (v : CW), Array.index_usize
      (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray toCurrent out) i = .ok v →
      AspisR1CurrentWide.Proof.CanonicalWide v := by
  exact AspisR1S9ActualPairPowersInvariantV1.powers_four_success_reads
    toCurrent AspisR1CurrentWide.Proof.CanonicalWide x out hx zero_canonical one_canonical
    (fun p p1 hp hmul => actual_wide_mul_success_canonical p x p1 hp hx hmul) hrun

/-- Native successful reads of the exact returned array inherit canonicality;
this form can be consumed directly by the actual Pair caller proof. -/
theorem actual_powers_four_native_reads_canonical
    (x : W) (out : Array W 4#usize) (hx : Canonical x)
    (hrun : AspisR1S9ProductionPairCutV1.weights.powers 4#usize x = .ok out) :
    ∀ (i : Usize) (v : W), Array.index_usize out i = .ok v → Canonical v := by
  intro i v hread
  have hm := AspisR1S9CandidateFoldMapPrimitivesV1.mapArray_index_result toCurrent out i
  rw [hread] at hm
  exact actual_powers_four_success_canonical x out hx hrun i (toCurrent v) hm.symm

#print axioms actual_powers_four_native_reads_canonical
#print axioms actual_powers_four_success_canonical
end AspisR1S9ActualPairPowersProducerV1
