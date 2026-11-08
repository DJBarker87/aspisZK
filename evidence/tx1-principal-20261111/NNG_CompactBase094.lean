import NNG_Tree094
import NNG_ScalarOps094
-- Adapted from NMT_R2_ConstantsA scalar-only decomposition; exact original source retained.
set_option autoImplicit false
namespace AspisR1.NNG_CompactBase094
open Aeneas Aeneas.Std
theorem semantic : NMT_tx1.verifier.SEMANTIC_BYTES = .ok 13831#usize := by
 unfold NMT_tx1.verifier.SEMANTIC_BYTES
 simp only [(AspisR1.NNG_ScalarOps094.mul 29#usize 32#usize 928#usize rfl),
  (AspisR1.NNG_ScalarOps094.add 12903#usize 928#usize 13831#usize rfl),
  bind_tc_ok]
#print axioms semantic
theorem values : NMT_tx1.compact.SEMANTIC_COMPACT_VALUES = .ok 426#usize := by
 unfold NMT_tx1.compact.SEMANTIC_COMPACT_VALUES
 simp only [(AspisR1.NNG_ScalarOps094.mul 10#usize 28#usize 280#usize rfl),
  (AspisR1.NNG_ScalarOps094.add 1#usize 280#usize 281#usize rfl),
  (AspisR1.NNG_ScalarOps094.add 87#usize 29#usize 116#usize rfl),
  (AspisR1.NNG_ScalarOps094.add 281#usize 116#usize 397#usize rfl),
  (AspisR1.NNG_ScalarOps094.add 397#usize 29#usize 426#usize rfl),
  bind_tc_ok]
#print axioms values

end AspisR1.NNG_CompactBase094
