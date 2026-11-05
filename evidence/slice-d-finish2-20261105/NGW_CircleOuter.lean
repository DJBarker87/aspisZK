import NGW_CircleInitial
set_option autoImplicit false
namespace NGW_CircleOuter
open Aeneas Aeneas.Std Result ControlFlow NGW_ConstructorQM NGW_ConstructorArrays NGW_FactorWrite

theorem source (z : Array NGW_CircleInitial.Point 2#usize) (factors : Factors)
 (e : Usize) (he : e.val ≤ 2) (hp : Holds NGW_CircleInitial.CanonPoint z) (hf : CanonFactors factors) :
 ∃ out,FIn_WeightsExtract.weights_new_loop1 {start:=e,«end»:=2#usize} z factors=ok out ∧ CanonFactors out := by
 let inv : (NGW_ForwardRange.Range × Factors) → Prop := fun s=>
   s.1.start.val ≤ s.1.end.val ∧ s.1.end=2#usize ∧ CanonFactors s.2
 have spec : WP.spec (FIn_WeightsExtract.weights_new_loop1 {start:=e,«end»:=2#usize} z factors) CanonFactors := by
  unfold FIn_WeightsExtract.weights_new_loop1
  apply loop.spec_decr_nat (fun s : NGW_ForwardRange.Range × Factors=>s.1.end.val-s.1.start.val)
    inv CanonFactors (fun s=>FIn_WeightsExtract.weights_new_loop1.body z s.1 s.2)
    ({start:=e,«end»:=2#usize},factors)
  · rintro ⟨iter,f⟩ ⟨order,finish,cf⟩
    change iter.start.val ≤ iter.end.val at order
    change iter.end=2#usize at finish
    have endpoint : iter.end.val=2 := by rw [finish];rfl
    change CanonFactors f at cf
    by_cases stop : iter.end.val ≤ iter.start.val
    · have advance := NGW_ForwardRange.done iter stop
      unfold NGW_ForwardRange.next at advance
      simp only [FIn_WeightsExtract.weights_new_loop1.body,advance,bind_tc_ok]
      dsimp! only
      rw [WP.spec_ok]
      exact cf
    · obtain ⟨rest,advance,increment,endEq⟩ := NGW_ForwardRange.active iter (by omega)
      have bk : iter.start.val < 2 := by omega
      obtain ⟨out,body,co⟩ := NGW_CircleInitial.source z f iter.start bk hp cf iter rest advance
      rw [body,WP.spec_ok]
      change (rest.start.val ≤ rest.end.val ∧ rest.end=2#usize ∧ CanonFactors out) ∧
        rest.end.val-rest.start.val < iter.end.val-iter.start.val
      exact ⟨⟨by rw [endEq,increment];omega,endEq.trans finish,co⟩,by rw [endEq,increment];omega⟩
  · exact ⟨he,rfl,hf⟩
 exact WP.spec_imp_exists spec

#print axioms source
end NGW_CircleOuter
