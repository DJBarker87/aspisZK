import RPu_FJh_ProjectedCallValue
import RPu_FIx_Builder
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJh_ProjectedArrayValue
open Aeneas Aeneas.Std Result FIq_Native
open FJh_Base (State QM Decode Canonical)
open FIv_PreparedNew (NP)
open FIw_ArrayValue (canonical decoded)
open FJa_PoseidonOrigins (Openings)
open FJh_ProjectedAfter (Packed)
abbrev callback := state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
/-- Each of the four outputs of the ORIGINAL constructor has its actual
callback value with the SAME ordered prepared weights. -/
theorem value (o : Openings) (internal : State) (theta : QM)
    (block : NP) (p : Array NP 3#usize) (lead full out : Packed) (w : Array QM 3#usize)
    (ct : canonical o.succ_z) (ci : canonical internal) (cb : Canonical theta)
    (cl : canonical lead) (cf : canonical full) (cw : canonical w)
    (rp : FIq_Native.core.array.Array.map (BuiltinFnMut QM NP) w field.PreparedQm31Multiplier.new=ok p)
    (rb : field.PreparedQm31Multiplier.new theta=ok block)
    (run : array_from_fn_copy 4#usize field.QM31.Insts.CoreMarkerCopy callback
      field.QM31.ZERO (o,internal,block,p,lead,full)=ok out) :
    canonical out ∧ decoded out=FJh_ProjectedCallValue.model o internal theta lead full w := by
  let model : Nat → FJh_Base.Exact := fun n=>if h : n<4 then
    FJh_ProjectedCallValue.model o internal theta lead full w ⟨n,h⟩ else 0
  have arr := FIx_Builder.fromFn 4#usize callback Canonical Decode model
    (o,internal,block,p,lead,full) out (by
      intro i hi x last call
      have hg : i.val<4 := hi
      have v := FJh_ProjectedCallValue.value o internal theta block p lead full w i hg x last
        ct ci cb cl cf cw rp rb call
      exact ⟨v.1,by simpa only [model,dif_pos hg] using v.2.1,v.2.2⟩) run
  refine ⟨arr.1,?_⟩
  funext g
  have eq := congrArg (fun xs : List FJh_Base.Exact=>xs[g.val]?) arr.2
  simp only [List.getElem?_map,List.getElem?_eq_getElem (by rw [out.property];exact g.isLt),
    Option.map_some,List.getElem?_ofFn,Fin.isLt,↓reduceDIte,model,dif_pos g.isLt] at eq
  have hg : g.val<4 := by simpa using g.isLt
  simp only [dif_pos hg] at eq
  exact Option.some.inj eq
#print axioms value
end AspisR1.FJh_ProjectedArrayValue
end
