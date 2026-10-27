import FJh_Native07RawValue
import FJh_Fin16Indices
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJk_ResidualLane
open FIv_NativeValue (K decode)
open FIw_ArrayValue (decoded)
open FJa_PoseidonOrigins (Openings Selectors)
attribute [local irreducible] R0P.poseidonLeadingPair
  R0P.poseidonInterpolatedFullPair R0P.poseidonInterpolatedInternalPair
/-- Pointwise identification; the three round values remain symbolic. -/
theorem value (o : Openings) (s : Selectors) (lane : Fin 16) :
    decode s.block *
      (decoded s.local ⟨0,by decide⟩ *
        (decoded o.succ_z lane-R0P.poseidonLeadingPair (decoded o.z) (decoded o.xor12_z) lane)+
      (decoded s.local ⟨1,by decide⟩+decoded s.local ⟨9,by decide⟩+decoded s.local ⟨10,by decide⟩)*
        (decoded o.succ_z lane-R0P.poseidonInterpolatedFullPair (decoded o.z) (decoded s.local) lane)+
      (List.ofFn (fun i : Fin 7=>decoded s.local ⟨i.val+2,by change i.val+2<16;omega⟩)).foldl (·+·) 0 *
        (decoded o.succ_z lane-R0P.poseidonInterpolatedInternalPair (decoded o.z) (decoded s.local) lane)) =
    R0P.poseidonScalarResidual (FJh_Native07RawValue.openings o) (decode s.block) (decoded s.local) lane := by
  unfold R0P.poseidonScalarResidual FJh_Native07RawValue.openings
  simp only [List.foldl_cons,List.foldl_nil,zero_add]
  congr 2 <;> try congr 2 <;> try congr 1
  all_goals try { apply congrArg (decoded s.local); apply Fin.ext; rfl }
  all_goals try rfl
#print axioms value
end AspisR1.FJk_ResidualLane
end
