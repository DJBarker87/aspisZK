import NGW_FactorWrite
import NGW_ForwardRange
import NGM_DoubleProduct
import NGW_ProductLaw
set_option autoImplicit false
namespace NGW_CircleCell
open Aeneas Aeneas.Std Result ControlFlow NGW_ConstructorQM NGW_ConstructorArrays NGW_FactorWrite

theorem source (factors : Factors) (k d : Usize) (x : Q)
 (hk : k.val<2) (hd : d.val<5) (hf : CanonFactors factors) (hx : Canon x)
 (iter rest : NGW_ForwardRange.Range) (advance : NGW_ForwardRange.next iter=ok (some d,rest)) :
 ∃ out next,FIn_WeightsExtract.weights_new_loop1_loop0.body k iter factors x=ok (cont (rest,out,next)) ∧ CanonFactors out ∧ Canon next := by
 obtain ⟨y,hy,cy⟩ := NGW_ConstructorQM.double x hx
 obtain ⟨product,hp,cp,_⟩ := NGW_ProductLaw.total x y hx cy
 obtain ⟨next,hn,cn⟩ := NGW_ConstructorQM.double y cy
 let row := Array.make 4#usize [FIn_WeightsExtract.field.QM31.ONE,x,y,product]
 have cr : CanonRow row := by
  intro q hq
  simp only [row,Array.make,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl|rfl|rfl|rfl
  · exact one
  · exact hx
  · exact cy
  · exact cp
 let kind := Usize.wrapping_add 3#usize k
 have bk : kind.val<5 := by
  have cases : k.val=0 ∨ k.val=1 := by omega
  rcases cases with h|h
  · have same : k=0#usize := UScalar.eq_of_val_eq h
    subst k
    decide
  · have same : k=1#usize := UScalar.eq_of_val_eq h
    subst k
    decide
 obtain ⟨out,write,co⟩ := NGW_FactorWrite.total factors kind d row bk hd hf cr
 refine ⟨out,next,?_,co,cn⟩
 unfold NGW_ForwardRange.next at advance
 unfold FIn_WeightsExtract.weights_new_loop1_loop0.body
 rw [advance]
 simp only [bind_tc_ok]
 dsimp! only
 simp only [hy,hp,lift,bind_tc_ok]
 unfold NGW_FactorWrite.write at write
 obtain ⟨v,hv,tail⟩ := AspisR1.Port3_PushFrame.bind_success _ _ _ write
 obtain ⟨p,hu,tail⟩ := AspisR1.Port3_PushFrame.bind_success _ _ _ tail
 rw [hv,bind_tc_ok,hu,bind_tc_ok,hn,bind_tc_ok]
 cases Result.ok.inj tail
 rfl

#print axioms source
end NGW_CircleCell
