import NGW_FactorCell
set_option autoImplicit false
namespace NGW_FactorLoops
open Aeneas Aeneas.Std Result ControlFlow NGW_ConstructorQM NGW_ConstructorArrays NGW_FactorWrite

theorem inner (points : Array (Array Q 10#usize) 3#usize) (factors : Factors)
 (k e : Usize) (hk : k.val<3) (he : e.val≤5)
 (hp : Holds (Holds Canon) points) (hf : CanonFactors factors) :
 ∃ out,FIn_WeightsExtract.weights_new_loop0_loop0 {start:=e,«end»:=5#usize} points factors k=ok out ∧ CanonFactors out := by
 let inv : (NGW_ForwardRange.Range × Factors) → Prop := fun s=>
   s.1.start.val≤s.1.end.val ∧ s.1.end=5#usize ∧ CanonFactors s.2
 have spec : WP.spec (FIn_WeightsExtract.weights_new_loop0_loop0 {start:=e,«end»:=5#usize} points factors k) CanonFactors := by
  unfold FIn_WeightsExtract.weights_new_loop0_loop0
  apply loop.spec_decr_nat (fun s : NGW_ForwardRange.Range × Factors=>s.1.end.val-s.1.start.val)
    inv CanonFactors (fun s=>FIn_WeightsExtract.weights_new_loop0_loop0.body points k s.1 s.2)
    ({start:=e,«end»:=5#usize},factors)
  · rintro ⟨iter,f⟩ ⟨order,finish,cf⟩
    change iter.start.val≤iter.end.val at order
    change iter.end=5#usize at finish
    change CanonFactors f at cf
    by_cases stop : iter.end.val≤iter.start.val
    · have advance := NGW_ForwardRange.done iter stop
      unfold NGW_ForwardRange.next at advance
      simp only [FIn_WeightsExtract.weights_new_loop0_loop0.body,advance,bind_tc_ok]
      dsimp! only
      rw [WP.spec_ok]
      exact cf
    · obtain ⟨rest,advance,increment,endEq⟩ := NGW_ForwardRange.active iter (by omega)
      have bd : iter.start.val<5 := by rw [finish] at order stop;change _<5;omega
      obtain ⟨out,body,co⟩ := NGW_FactorCell.source points f k iter.start hk bd hp cf iter rest advance
      rw [body,WP.spec_ok]
      change (rest.start.val≤rest.end.val ∧ rest.end=5#usize ∧ CanonFactors out) ∧
        rest.end.val-rest.start.val<iter.end.val-iter.start.val
      exact ⟨⟨by rw [endEq,increment];omega,endEq.trans finish,co⟩,by rw [endEq,increment];omega⟩
  · exact ⟨he,rfl,hf⟩
 exact WP.spec_imp_exists spec

#print axioms inner
end NGW_FactorLoops
