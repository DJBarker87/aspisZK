import FJh_ProjectedArrayValue
import FJh_Fin16Indices
import FJh_ResidualModel
import FJh_InternalPairValue
import FJe_PackedValues
import FJh_LowModels
import FJh_PackResidual
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJh_Native07RawValue
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
open FIw_ArrayValue (canonical decoded)
open FJa_PoseidonOrigins (Openings Selectors)
open ExtractedMaskQmPackBase4Arithmetic (iBasis uBasis)
attribute [local irreducible] R0P.poseidonLeadingPair
  R0P.poseidonInterpolatedFullPair R0P.poseidonInterpolatedInternalPair
def openings (o : Openings) : R0P.Openings K :=
  ⟨decoded o.z,decoded o.succ_z,decoded o.xor12_z⟩
def model (o : Openings) (s : Selectors) (g : Fin 4) : K :=
  let pack (v : Fin 16 → K) := R0P.poseidonPackingFormula iBasis uBasis
    (fun j=>v (FJe_ExternalAdjoint.lane g j))
  decode s.block *
    (decoded s.local ⟨(0#usize).val,by decide⟩ *
        (pack (decoded o.succ_z)-pack (R0P.poseidonLeadingPair (decoded o.z) (decoded o.xor12_z)))+
      (decoded s.local ⟨1,by decide⟩+decoded s.local ⟨9,by decide⟩+decoded s.local ⟨10,by decide⟩)*
        (pack (decoded o.succ_z)-pack (R0P.poseidonInterpolatedFullPair (decoded o.z) (decoded s.local)))+
      (List.ofFn (fun i : Fin 7=>decoded s.local ⟨i.val+2,by change i.val+2<16;omega⟩)).foldl (·+·) 0 *
        (pack (decoded o.succ_z)-pack (R0P.poseidonInterpolatedInternalPair (decoded o.z) (decoded s.local))))
/-- Complete original Native07 arithmetic VALUE in explicit native packing
form. Identification with R0P scalarResidual is a separate model join. -/
theorem value (o : Openings) (s : Selectors) (out : Array NQ 4#usize)
    (hz : canonical o.z) (ht : canonical o.succ_z) (hx : canonical o.xor12_z)
    (hs : canonical s.local) (hb : Canon s.block)
    (run : state_only_poseidon.evaluate_state_only_poseidon_oracle_projected o s=ok out) :
    canonical out ∧ decoded out=model o s := by
  obtain ⟨l0,f0,i0,leading,full,internal,p,block,rl0,rf0,ri0,rl,rf,ri,rp,rb,ra⟩ :=
    FJa_PoseidonOrigins.reached o s out run
  have vl := FJe_PackedValues.leading o leading hz hx rl
  have vf := FJe_PackedValues.full o.z s.local full hz hs rf
  have vi := FJh_InternalPairValue.value o.z s.local internal hz hs ri
  have cl0 := FIv_NativeArray.canonical s.local 0#usize l0 hs rl0
  have vf0 := FJa_FullLowWeight.value s f0 hs rf0
  have vi0 := FJa_InternalLowWeight.value s i0 hs ri0
  let w := Array.make 3#usize [l0,f0,i0]
  have cw : canonical w := by
    intro x hx
    simp only [w,Array.make,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl
    · exact cl0
    · exact vf0.1
    · exact vi0.1
  have va := FJh_ProjectedArrayValue.value o internal s.block block p leading full out w
    ht vi.1 hb vl.1 vf.1 cw rp rb ra
  have low0 := FIw_ArrayReadValue.read s.local 0#usize (by decide) l0 rl0
  have low1 : decode f0=decoded s.local ⟨1,by decide⟩+decoded s.local ⟨9,by decide⟩+
      decoded s.local ⟨10,by decide⟩ := by
    rw [vf0.2,FJh_LowModels.cell s.local 1 (by decide),
      FJh_LowModels.cell s.local 9 (by decide),FJh_LowModels.cell s.local 10 (by decide)]
  have low2 := vi0.2.trans (FJh_LowModels.internal s)
  refine ⟨va.1,?_⟩
  funext g
  rw [va.2]
  unfold FJh_ProjectedCallValue.model
  change decode s.block*(decode l0*(FJh_SlicePackValue.pack o.succ_z g-decoded leading g)+
    decode f0*(FJh_SlicePackValue.pack o.succ_z g-decoded full g)+
    decode i0*(FJh_SlicePackValue.pack o.succ_z g-FJh_SlicePackValue.pack internal g))=_
  rw [low0,low1,low2,vl.2,vf.2]
  unfold FJh_SlicePackValue.pack
  rw [vi.2]
  rfl
#print axioms value
end AspisR1.FJh_Native07RawValue
end
