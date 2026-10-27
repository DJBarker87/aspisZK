import RPu_FJe_PackedRawTable
import RPu_FJe_PackedRawAfter
import RPu_FJe_PackedBound
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJe_PackedRawOrigins
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
/-- The SAME actual mapped input,nested matrix table,offset,and arithmetic
suffix of the original successful raw packed call. -/
theorem value (input : Array NQ 4#usize) (out : Array U64 4#usize)
    (run : state_only_poseidon.external_local_packed_raw input=ok out) :
    ∃ (mapped : FJb_RawRowCallbacks.Input) (table : FJe_PackedRawTable.Table) (bound : U64),
      FIq_Native.core.array.Array.map (BuiltinFnMut NQ (Array U32 4#usize))
        input state_only_poseidon.extension_limbs=ok mapped ∧
      FJe_PackedRawTable.construct mapped=ok table ∧
      state_only_poseidon.EXTERNAL_LOCAL_LIMB_MODULUS_BOUND=ok bound ∧
      FJe_PackedRawAfter.source table bound=ok out := by
  unfold state_only_poseidon.external_local_packed_raw at run
  obtain ⟨mapped,hm,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨table,ht,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨u,_,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨bound,hb,tail⟩ := FIv_Map.bind_success _ _ _ run
  exact ⟨mapped,table,bound,hm,ht,hb,tail⟩
#print axioms value
end AspisR1.FJe_PackedRawOrigins
end
