import NCJ_Permutation
import NCJ_CellCanon
import NBG_WideCarriers
set_option autoImplicit false
noncomputable section
namespace NCJ_ScalarCellTotal
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues
abbrev Closure := FIo_Native.weights.Weights.scalar_factor.closure
abbrev call := FIo_Native.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact.call_mut

theorem source (p : Array NE 4#usize) (f : Array NQ 4#usize)
    (hp : ∀ x∈p.val,canonE x) (v : NE) (hv : canonE v) (s : Usize) (hs : s.val<4) :
    ∃ out,call (p,f) (v,s)=ok (out,(p,f)) ∧ canonE out := by
  obtain ⟨i,perm,_,ib⟩ := NCJ_Permutation.source s hs
  let pv := NCJ_GuardExact.pick p i.val ib
  let fv := NCJ_GuardExact.pick f s.val hs
  have pr := NCJ_GuardExact.index p i ib
  have fr := NCJ_GuardExact.index f s hs
  change Array.index_usize p i=ok pv at pr
  change Array.index_usize f s=ok fv at fr
  have cp : canonE pv := by
    apply hp
    exact List.mem_of_getElem? (show p.val[i.val]?=some pv by
      simp [pv,NCJ_GuardExact.pick,show i.val< p.val.length by rw [p.property];exact ib])
  obtain ⟨product,mul,cm,_⟩ := NBG_FieldDischarge.wide_qm pv fv cp
  obtain ⟨out,add,co,_⟩ := NBG_WideCarriers.wide_add v product hv cm
  refine ⟨out,?_,co⟩
  change (do
    let index ← Array.index_usize FIo_Native.weights.PERM s
    let a ← Array.index_usize p index
    let b ← Array.index_usize f s
    let product ← FIo_Native.aspis_core.field.wide_exact.WideExact.mul_qm31 a b
    let out ← FIo_Native.aspis_core.field.wide_exact.WideExact.add v product
    ok (out,(p,f)))=ok (out,(p,f))
  simp only [perm,pr,fr,mul,add,bind_tc_ok]

#print axioms source
end NCJ_ScalarCellTotal
