import OccupancyGeneratedSlice
import ExtractedMaskQM31Exact
import ScheduleDomainArithmetic

/-! Generic actual terminal lift_m31 source contract. Canonicality requires
the real source M31 bound; scalar interpretation itself is structural. -/
set_option autoImplicit false
namespace AspisR1.TerminalLiftM31Exact
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.ExtractedMaskQM31Exact
abbrev QM := field.QM31
abbrev P := AspisR1.ExtractedMaskTowerAdd.P
abbrev Canonical := CurrentCanonicalQM

def lifted (m : field.M31) : QM := ⟨⟨m, 0#u32⟩, ⟨0#u32, 0#u32⟩⟩

theorem lift_source_eq (m : field.M31) :
    pool_v1.pair_forest_semantic_terminal.lift_m31 m = .ok (lifted m) := by
  simp only [pool_v1.pair_forest_semantic_terminal.lift_m31, field.CM31.from_m31,
    field.QM31.from_cm31, field.CM31.ZERO, field.M31.ZERO, bind_tc_ok, lifted]

theorem lifted_canonical (m : field.M31) (hm : m.val < P) : Canonical (lifted m) := by
  change (m.val < P ∧ (0#u32).val < P) ∧ ((0#u32).val < P ∧ (0#u32).val < P)
  have hz : (0#u32).val < P := by
    norm_num [P, AspisR1.ExtractedMaskTowerAdd.P, AspisR1.ExtractedMaskM31AddSub.P]
  exact ⟨⟨hm, hz⟩, hz, hz⟩

theorem lift_source_exact (m : field.M31) (hm : m.val < P) :
    ∃ q, pool_v1.pair_forest_semantic_terminal.lift_m31 m = .ok q ∧
      Canonical q ∧ decode q = (m.val : AspisV8R15.ExactTowerBase.QM31Exact) := by
  refine ⟨lifted m, lift_source_eq m, lifted_canonical m hm, ?_⟩
  have h : decode (lifted m) = AspisR1.ExtractedMaskScalarExact.scalarEmbedding m := rfl
  exact h.trans (AspisR1.ScheduleDomainArithmetic.scalarEmbedding_nat m)

#print axioms lift_source_eq
#print axioms lifted_canonical
#print axioms lift_source_exact
end AspisR1.TerminalLiftM31Exact
