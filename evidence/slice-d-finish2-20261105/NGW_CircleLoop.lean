import NGW_CircleCell
set_option autoImplicit false
namespace NGW_CircleLoop
open Aeneas Aeneas.Std Result ControlFlow NGW_ConstructorQM NGW_FactorWrite

theorem source (factors : Factors) (k e : Usize) (x : Q)
 (hk : k.val < 2) (he : e.val ≤ 5) (hf : CanonFactors factors) (hx : Canon x) :
 ∃ out,FIn_WeightsExtract.weights_new_loop1_loop0 {start:=e,«end»:=5#usize} factors k x=ok out ∧ CanonFactors out := by
 let inv : (NGW_ForwardRange.Range × Factors × Q) → Prop := fun s=>
   s.1.start.val ≤ s.1.end.val ∧ s.1.end=5#usize ∧ CanonFactors s.2.1 ∧ Canon s.2.2
 have spec : WP.spec (FIn_WeightsExtract.weights_new_loop1_loop0 {start:=e,«end»:=5#usize} factors k x) CanonFactors := by
  unfold FIn_WeightsExtract.weights_new_loop1_loop0
  apply loop.spec_decr_nat (fun s : NGW_ForwardRange.Range × Factors × Q=>s.1.end.val-s.1.start.val)
    inv CanonFactors (fun s=>FIn_WeightsExtract.weights_new_loop1_loop0.body k s.1 s.2.1 s.2.2)
    ({start:=e,«end»:=5#usize},factors,x)
  · rintro ⟨iter,f,carry⟩ ⟨order,finish,cf,cc⟩
    change iter.start.val ≤ iter.end.val at order
    change iter.end=5#usize at finish
    have endpoint : iter.end.val=5 := by rw [finish];rfl
    change CanonFactors f at cf
    change Canon carry at cc
    by_cases stop : iter.end.val ≤ iter.start.val
    · have advance := NGW_ForwardRange.done iter stop
      unfold NGW_ForwardRange.next at advance
      simp only [FIn_WeightsExtract.weights_new_loop1_loop0.body,advance,bind_tc_ok]
      dsimp! only
      rw [WP.spec_ok]
      exact cf
    · obtain ⟨rest,advance,increment,endEq⟩ := NGW_ForwardRange.active iter (by omega)
      have bd : iter.start.val < 5 := by omega
      obtain ⟨out,next,body,co,cn⟩ := NGW_CircleCell.source f k iter.start carry hk bd cf cc iter rest advance
      rw [body,WP.spec_ok]
      change (rest.start.val ≤ rest.end.val ∧ rest.end=5#usize ∧ CanonFactors out ∧ Canon next) ∧
        rest.end.val-rest.start.val < iter.end.val-iter.start.val
      exact ⟨⟨by rw [endEq,increment];omega,endEq.trans finish,co,cn⟩,by rw [endEq,increment];omega⟩
  · exact ⟨he,rfl,hf,hx⟩
 exact WP.spec_imp_exists spec

#print axioms source
end NGW_CircleLoop
