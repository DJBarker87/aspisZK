import RPv_FIx_ValueConservationSource
import RPu_FIw_WordValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIx_ConservationMeaning
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K decode)
open FIw_ArrayValue (canonical)
open FIx_ValueConservationSource (Openings Selectors)

theorem index (base row : Usize)
    (hb : 16#usize*pool_v1.pair_forest_semantic_terminal.VALUE_AUXILIARY_BLOCK=ok base)
    (hr : base+6#usize=ok row) : row.val=1014 := by
  have vb := FIw_WordValue.mul 16#usize pool_v1.pair_forest_semantic_terminal.VALUE_AUXILIARY_BLOCK base hb
  have vr := FIw_WordValue.add base 6#usize row hr
  rw [vb,pool_v1.pair_forest_semantic_terminal.VALUE_AUXILIARY_BLOCK] at vr
  exact vr

theorem value (packed out : Array NQ 24#usize) (o : Openings) (s : Selectors)
    (hz : canonical o.z) (hs : canonical o.succ_z) (hx : canonical o.xor12_z)
    (hh : canonical s.high) (hl : canonical s.low)
    (success : pool_v1.pair_forest_semantic_terminal.add_value_lanes packed o s=ok out) :
    ∃ (before : Array NQ 24#usize) (scalars : Array NQ 2#usize),
      pool_v1.pair_forest_semantic_terminal.add_preweighted before 82#usize scalars=ok out ∧
      canonical scalars ∧ scalars.val.map decode=FIx_ValueConservation.model
        (FIv_NativeArray.value s.high 63*FIv_NativeArray.value s.low 6)
        (FIv_NativeArray.value o.z) (FIv_NativeArray.value o.succ_z) := by
  obtain ⟨before,selector,row,base,scalars,hbase,hrow,hselector,hscalar,tail,hcanon,meaning⟩ :=
    FIx_ValueConservationSource.value packed out o s hz hs hx hh hl success
  have rowValue := index base row hbase hrow
  refine ⟨before,scalars,tail,hcanon,?_⟩
  rw [meaning,rowValue]
#print axioms index
#print axioms value
end AspisR1.FIx_ConservationMeaning
end
