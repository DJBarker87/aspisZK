import NGW_FactorIndex
import NGW_FactorWrite
import NGW_ForwardRange
set_option autoImplicit false
namespace NGW_FactorCell
open Aeneas Aeneas.Std Result ControlFlow NGW_ConstructorQM NGW_ConstructorArrays NGW_FactorWrite

theorem source (points : Array (Array Q 10#usize) 3#usize) (factors : Factors)
 (k d : Usize) (hk : k.val<3) (hd : d.val<5)
 (hp : Holds (Holds Canon) points) (hf : CanonFactors factors)
 (iter rest : NGW_ForwardRange.Range)
 (advance : NGW_ForwardRange.next iter=ok (some d,rest)) :
 ∃ out,FIn_WeightsExtract.weights_new_loop0_loop0.body points k iter factors=ok (cont (rest,out)) ∧ CanonFactors out := by
 obtain ⟨t,ht,bt⟩ := NGW_FactorIndex.tau d hd
 have bounds := NGW_FactorIndex.coordinates t bt
 let ia := Usize.wrapping_sub 9#usize (Usize.wrapping_mul 2#usize t)
 let ib := Usize.wrapping_sub 8#usize (Usize.wrapping_mul 2#usize t)
 let prow := NGM_GuardExact.pick points k.val hk
 have readp := NGM_GuardExact.index points k hk
 change Array.index_usize points k=ok prow at readp
 have cp := canonical_pick (Holds Canon) points k.val hk hp
 let a := NGM_GuardExact.pick prow ia.val bounds.1
 let b := NGM_GuardExact.pick prow ib.val bounds.2
 have ra := NGM_GuardExact.index prow ia bounds.1
 have rb := NGM_GuardExact.index prow ib bounds.2
 have readA : Array.index_usize prow (Usize.wrapping_sub 9#usize (Usize.wrapping_mul 2#usize t))=ok a := ra
 have readB : Array.index_usize prow (Usize.wrapping_sub 8#usize (Usize.wrapping_mul 2#usize t))=ok b := rb
 have ca := canonical_pick Canon prow ia.val bounds.1 cp
 have cb := canonical_pick Canon prow ib.val bounds.2 cp
 obtain ⟨aa,bb,p0,p1,p2,p3,haa,_,hbb,_,h0,h1,h2,h3,_,canon⟩ := NGW_FactorRow.total a b ca cb
 let row := Array.make 4#usize [p0,p1,p2,p3]
 obtain ⟨out,write,co⟩ := NGW_FactorWrite.total factors k d row (by omega) hd hf canon
 refine ⟨out,?_,co⟩
 unfold NGW_ForwardRange.next at advance
 unfold FIn_WeightsExtract.weights_new_loop0_loop0.body
 rw [advance]
 simp only [bind_tc_ok]
 dsimp! only
 simp only [ht,readp,readA,readB,haa,hbb,h0,h1,h2,h3,lift,bind_tc_ok]
 unfold NGW_FactorWrite.write at write
 obtain ⟨plane,mutable,tail⟩ := AspisR1.Port3_PushFrame.bind_success _ _ _ write
 obtain ⟨next,update,tail⟩ := AspisR1.Port3_PushFrame.bind_success _ _ _ tail
 rw [mutable,bind_tc_ok,update,bind_tc_ok]
 cases Result.ok.inj tail
 rfl

#print axioms source
end NGW_FactorCell
