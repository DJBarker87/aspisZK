import RPu_FJl_QMCodec
import RPv_FJn_MainTerminal
import R1PublicSourceRawMap
set_option autoImplicit false
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
