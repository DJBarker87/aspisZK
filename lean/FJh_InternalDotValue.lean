import FJh_M31DotSevenExact
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJh_InternalDotValue
open Aeneas Aeneas.Std Result FIq_Native
open FJh_Base (QM Canonical Decode Exact cell P)
theorem value (w : Array QM 7#usize) (c : Array U32 7#usize) (out : QM)
    (cw : FIw_ArrayValue.canonical w) (cc : ∀i : Fin 7,(cell c i).val<P)
    (run : field.qm31_m31_dot (Array.to_slice w) (Array.to_slice c)=ok out) :
    Canonical out ∧ Decode out=(List.ofFn (fun i : Fin 7=>
      Decode (cell w i)*((cell c i).val : Exact))).foldl (·+·) 0 := by
  obtain ⟨v,rv,cv,vv⟩ := FJh_M31DotSevenExact.source_success (Array.to_slice w) (Array.to_slice c)
    w.property c.property (by
      intro i hi
      exact cw _ (List.getElem_mem _)) (by
      intro i hi
      exact cc ⟨i,by simpa [Array.to_slice,c.property] using hi⟩)
  have eq : v=out := Result.ok.inj (rv.symm.trans run)
  subst v
  exact ⟨cv,vv⟩
#print axioms value
end AspisR1.FJh_InternalDotValue
end
