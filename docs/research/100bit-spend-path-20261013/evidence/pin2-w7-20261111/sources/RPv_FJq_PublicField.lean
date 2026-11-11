import RPu_FJl_QMCodec
import RPv_FIz_ConcretePack
import R1ExactBaseProjection
import R1PublicSourceRawMap
set_option autoImplicit false
/-! PIN2 W11 (2026-11-11), coordinator-approved: import narrowed, no statement change.
The release module imported `RPv_FJn_MainTerminal` but uses nothing from it; it is replaced by
`RPv_FIz_ConcretePack` (for `embed`) and `R1ExactBaseProjection`, so the FJq public chain no
longer waits on the FJn terminal restatement. Statement and proof text unchanged. -/
noncomputable section
namespace AspisR1.FJq_PublicField
open FIz_ConcretePack (embed)
/-- Guarded raw public word and its literal parser image embed identically. -/
theorem value (x : PublicSourceRaw.Word) (h : PublicSourceRaw.fieldCanonical x) :
    ExactBaseProjection.embed (PublicSourceRaw.mapField x h)=embed (x.val : FIv_NativeValue.K) := by
  unfold PublicSourceRaw.mapField
  rw [FJl_QMCodec.residue]
  simp only [map_natCast]
#print axioms value
end AspisR1.FJq_PublicField
end
