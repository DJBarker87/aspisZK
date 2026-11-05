import NGW_FactorLoops
set_option autoImplicit false
namespace NGW_FactorOuter
open Aeneas Aeneas.Std Result ControlFlow NGW_ConstructorQM NGW_ConstructorArrays NGW_FactorWrite

theorem source (points : Array (Array Q 10#usize) 3#usize) (factors : Factors)
 (e : Usize) (he : e.val ≤ 3) (hp : Holds (Holds Canon) points) (hf : CanonFactors factors) :
 ∃ out,FIn_WeightsExtract.weights_new_loop0 {start:=e,«end»:=3#usize} points factors=ok out ∧ CanonFactors out := by
 let inv : (NGW_ForwardRange.Range × Factors) → Prop := fun s=>
   s.1.start.val ≤ s.1.end.val ∧ s.1.end=3#usize ∧ CanonFactors s.2
 have spec : WP.spec (FIn_WeightsExtract.weights_new_loop0 {start:=e,«end»:=3#usize} points factors) CanonFactors := by
  unfold FIn_WeightsExtract.weights_new_loop0
  apply loop.spec_decr_nat (fun s : NGW_ForwardRange.Range × Factors=>s.1.end.val-s.1.start.val)
    inv CanonFactors (fun s=>FIn_WeightsExtract.weights_new_loop0.body points s.1 s.2)
    ({start:=e,«end»:=3#usize},factors)
  · rintro ⟨iter,f⟩ ⟨order,finish,cf⟩
    change iter.start.val ≤ iter.end.val at order
    change iter.end=3#usize at finish
    have endpoint : iter.end.val=3 := by rw [finish];rfl
    change CanonFactors f at cf
    by_cases stop : iter.end.val ≤ iter.start.val
    · have advance := NGW_ForwardRange.done iter stop
      unfold NGW_ForwardRange.next at advance
      simp only [FIn_WeightsExtract.weights_new_loop0.body,advance,bind_tc_ok]
      dsimp! only
      rw [WP.spec_ok]
      exact cf
    · obtain ⟨rest,advance,increment,endEq⟩ := NGW_ForwardRange.active iter (by omega)
      have bk : iter.start.val < 3 := by omega
      obtain ⟨out,inner,co⟩ := NGW_FactorLoops.inner points f iter.start 0#usize bk (by decide) hp cf
      unfold NGW_ForwardRange.next at advance
      simp only [FIn_WeightsExtract.weights_new_loop0.body,advance,bind_tc_ok]
      dsimp! only
      rw [inner]
      simp only [bind_tc_ok,WP.spec_ok]
      change (rest.start.val ≤ rest.end.val ∧ rest.end=3#usize ∧ CanonFactors out) ∧
        rest.end.val-rest.start.val < iter.end.val-iter.start.val
      exact ⟨⟨by rw [endEq,increment];omega,endEq.trans finish,co⟩,by rw [endEq,increment];omega⟩
  · exact ⟨he,rfl,hf⟩
 exact WP.spec_imp_exists spec

#print axioms source
end NGW_FactorOuter
