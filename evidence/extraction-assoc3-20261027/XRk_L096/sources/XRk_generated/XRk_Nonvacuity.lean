import XRk_Tx1Association
import XRk_EmptyGeometry
open Aeneas Aeneas.Std Result
open XRk_Release
namespace XRk_Nonvacuity
/- Nonempty local carriers; this is deliberately not whole-top non-vacuity. -/
theorem canonical_zero_domain :
    ∃ q : aspis_core.field.QM31,
      q.c0.a < 2147483647#u32 ∧ q.c0.b < 2147483647#u32 ∧
      q.c1.a < 2147483647#u32 ∧ q.c1.b < 2147483647#u32 := by
  exact ⟨XRk_FieldExternal.qzero,by decide,by decide,by decide,by decide⟩
theorem below_dot_bound :
    ∃ s : fast_pairing.EbyKDot, s.count < 4096#usize := by
  exact ⟨⟨XRk_dotZero,XRk_dotZero,0#usize⟩,by scalar_tac⟩
theorem invalid_row_is_reached :
    r1_wire.ValidatedRecord.decode_k 0#usize ⟨0#u8,⟨[],by simp⟩⟩ 0#usize = ok (.Err .InvalidRow) := by
  rfl
theorem accepted_empty_geometry :
    ∃ g : verifier.QueryGeometry,
      verifier.QueryGeometry.for_range_loop0 ⟨XRk_EmptyGeometry.emptySlice,0⟩ 0#usize
        XRk_EmptyGeometry.emptyValues XRk_EmptyGeometry.emptyValues=ok (.Ok g) :=
  ⟨XRk_EmptyGeometry.emptyGeometry 0#usize,XRk_EmptyGeometry.run 0#usize⟩
#print axioms accepted_empty_geometry
#print axioms canonical_zero_domain
#print axioms below_dot_bound
#print axioms invalid_row_is_reached
end XRk_Nonvacuity
