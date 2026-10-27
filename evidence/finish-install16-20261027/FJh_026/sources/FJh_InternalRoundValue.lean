import FJh_InternalLinearExact
import FJa_PoseidonPow5
import FIw_ArrayReadValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJh_InternalRoundValue
open Aeneas Aeneas.Std Result FIq_Native
open FJh_Base (State QM CanonicalState Canonical Decode cell)
open FIw_ArrayValue (canonical decoded)
theorem value (s out : State) (c : QM) (hs : canonical s) (hc : Canonical c)
    (run : state_only_poseidon.internal_round s c=ok out) :
    canonical out ∧ decoded out=R0P.poseidonInternalRound (decoded s) (Decode c) := by
  unfold state_only_poseidon.internal_round at run
  obtain ⟨q,rq,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨added,ra,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨powered,rp,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨next,rn,run⟩ := FIv_Map.bind_success _ _ _ run
  have va := FIv_NativeValue.add q c added (FIv_NativeArray.canonical s 0#usize q hs rq) hc ra
  have vp := FJa_PoseidonPow5.value added powered va.1 rp
  have vn := FIw_ArrayValue.update s next 0#usize powered (by decide) hs vp.1 rn
  have hn : CanonicalState next := by
    intro i
    exact vn.1 _ (List.getElem_mem _)
  obtain ⟨expected,re,ce,ve⟩ := FJh_InternalLinearExact.source_success next hn
  have eq : expected=out := Result.ok.inj (re.symm.trans run)
  subst expected
  have co : canonical out := by
    intro x hx
    obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hx
    exact ce ⟨j,by simpa [out.property] using hj⟩
  refine ⟨co,?_⟩
  have hv : decoded out=R0P.poseidonInternalLinear (decoded next) := funext ve
  have hd : decoded next=(fun j : Fin 16=>if j=0 then
      R0P.poseidonPow5 (decoded s ⟨0,by decide⟩+Decode c) else decoded s j) := by
    rw [vn.2,vp.2,va.2,FIw_ArrayReadValue.read s 0#usize (by decide) q rq]
    funext j
    change (if j=(0 : Fin 16) then
      (decoded s ⟨0,by decide⟩+Decode c)^5 else decoded s j)=_
    by_cases hj : j=(0 : Fin 16)
    · simp only [if_pos hj,R0P.poseidonPow5];ring
    · simp only [if_neg hj]
  exact hv.trans (congrArg R0P.poseidonInternalLinear hd)
#print axioms value
end AspisR1.FJh_InternalRoundValue
end
