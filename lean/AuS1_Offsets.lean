import AuS1_ViewSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.AuS1_Offsets
open Aeneas Aeneas.Std Result
open AspisR1SelectedWideViewV1

 theorem add (a b c : Usize) (fits : a.val + b.val ≤ Usize.max)
    (value : c.val = a.val + b.val) : a + b = ok c := by
  obtain ⟨out,call,fields⟩ := WP.spec_imp_exists (Usize.add_spec (x:=a) (y:=b) fits)
  have same : out = c := by scalar_tac
  simpa only [same] using call

 theorem mul (a b c : Usize) (fits : a.val * b.val ≤ Usize.max)
    (value : c.val = a.val * b.val) : a * b = ok c := by
  obtain ⟨out,call,fields⟩ := WP.spec_imp_exists (Usize.mul_spec (x:=a) (y:=b) fits)
  have same : out = c := by scalar_tac
  simpa only [same] using call

 theorem sub (a b c : Usize) (fits : b.val ≤ a.val)
    (value : c.val = a.val - b.val) : a - b = ok c := by
  obtain ⟨out,call,fields⟩ := WP.spec_imp_exists (Usize.sub_spec (x:=a) (y:=b) fits)
  have same : out = c := by scalar_tac
  simpa only [same] using call

 theorem semantic_values : compact.SEMANTIC_COMPACT_VALUES = ok 426#usize := by
  unfold compact.SEMANTIC_COMPACT_VALUES
  rw [mul 10#usize 28#usize 280#usize (by scalar_tac) (by scalar_tac)]
  simp only [bind_tc_ok]
  rw [add 1#usize 280#usize 281#usize (by scalar_tac) (by scalar_tac)]
  simp only [bind_tc_ok]
  rw [add 87#usize 29#usize 116#usize (by scalar_tac) (by scalar_tac)]
  simp only [bind_tc_ok]
  rw [add 281#usize 116#usize 397#usize (by scalar_tac) (by scalar_tac)]
  simp only [bind_tc_ok]
  exact add _ _ _ (by scalar_tac) (by scalar_tac)

 theorem logical : compact.LOGICAL_SEMANTIC = ok 13831#usize := by
  unfold compact.LOGICAL_SEMANTIC verifier.SEMANTIC_BYTES
  rw [mul 29#usize 32#usize 928#usize (by scalar_tac) (by scalar_tac)]
  simp only [bind_tc_ok]
  exact add _ _ _ (by scalar_tac) (by scalar_tac)

 theorem semantic : compact.COMPACT_SEMANTIC = ok 7015#usize := by
  unfold compact.COMPACT_SEMANTIC
  rw [semantic_values]
  simp only [bind_tc_ok]
  rw [mul 16#usize 426#usize 6816#usize (by scalar_tac) (by scalar_tac),logical]
  simp only [bind_tc_ok]
  exact sub _ _ _ (by scalar_tac) (by scalar_tac)

 theorem y1 : compact.OFF_Y1 = ok 7031#usize := by
  unfold compact.OFF_Y1
  rw [semantic]
  simp only [bind_tc_ok,compact.OFF_SEMANTIC,compact.HEADER]
  exact add _ _ _ (by scalar_tac) (by scalar_tac)

 theorem y1_size : compact.COMPACT_Y1 = ok 464#usize := by
  unfold compact.COMPACT_Y1
  exact mul _ _ _ (by scalar_tac) (by scalar_tac)

 theorem inactive : compact.OFF_INACTIVE = ok 7495#usize := by
  unfold compact.OFF_INACTIVE
  rw [y1,y1_size]
  simp only [bind_tc_ok]
  exact add _ _ _ (by scalar_tac) (by scalar_tac)

 theorem round0 : compact.OFF_ROUND0 = ok 7527#usize := by
  unfold compact.OFF_ROUND0
  rw [inactive]
  simp only [bind_tc_ok]
  exact add _ _ _ (by scalar_tac) (by scalar_tac)

 theorem folded : compact.OFF_FOLDED_ROOT = ok 7751#usize := by
  unfold compact.OFF_FOLDED_ROOT
  rw [round0]
  simp only [bind_tc_ok]
  exact add _ _ _ (by scalar_tac) (by scalar_tac)

 theorem round1 : compact.OFF_ROUND1 = ok 7783#usize := by
  unfold compact.OFF_ROUND1
  rw [folded]
  simp only [bind_tc_ok]
  exact add _ _ _ (by scalar_tac) (by scalar_tac)

#print axioms add
#print axioms mul
#print axioms sub
#print axioms semantic_values
#print axioms logical
#print axioms semantic
#print axioms y1
#print axioms y1_size
#print axioms inactive
#print axioms round0
#print axioms folded
#print axioms round1
end AspisR1.AuS1_Offsets
end
