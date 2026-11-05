import NGW_KindIndex
import NGW_CircleLoop
import NGW_ConstructorArrays
set_option autoImplicit false
namespace NGW_CircleInitial
open Aeneas Aeneas.Std Result ControlFlow NGW_ConstructorQM NGW_ConstructorArrays NGW_FactorWrite
abbrev Point := FIn_WeightsExtract.circle.SecureCirclePoint
def CanonPoint (p : Point) : Prop := Canon p.x ∧ Canon p.y

theorem source (z : Array Point 2#usize) (factors : Factors) (k : Usize)
 (hk : k.val < 2) (hz : Holds CanonPoint z) (hf : CanonFactors factors)
 (iter rest : NGW_ForwardRange.Range) (advance : NGW_ForwardRange.next iter=ok (some k,rest)) :
 ∃ out,FIn_WeightsExtract.weights_new_loop1.body z iter factors=ok (cont (rest,out)) ∧ CanonFactors out := by
 let point := NGM_GuardExact.pick z k.val hk
 have read := NGM_GuardExact.index z k hk
 change Array.index_usize z k=ok point at read
 have cp := canonical_pick CanonPoint z k.val hk hz
 obtain ⟨product,hp,canonical,_⟩ := NGW_ProductLaw.total point.x point.y cp.1 cp.2
 obtain ⟨x,hx,cx⟩ := NGW_ConstructorQM.double point.x cp.1
 let row := Array.make 4#usize [FIn_WeightsExtract.field.QM31.ONE,point.y,point.x,product]
 have cr : CanonRow row := by
  intro q hq
  simp only [row,Array.make,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl|rfl|rfl|rfl
  · exact one
  · exact cp.2
  · exact cp.1
  · exact canonical
 let kind := Usize.wrapping_add 3#usize k
 have bk : kind.val < 5 := NGW_KindIndex.bound k hk
 obtain ⟨first,write,cf⟩ := NGW_FactorWrite.total factors kind 0#usize row bk (by decide) hf cr
 obtain ⟨out,inner,co⟩ := NGW_CircleLoop.source first k 1#usize x hk (by decide) cf cx
 refine ⟨out,?_,co⟩
 unfold NGW_ForwardRange.next at advance
 unfold FIn_WeightsExtract.weights_new_loop1.body
 rw [advance]
 simp only [bind_tc_ok]
 dsimp! only
 simp only [read,hp,lift,bind_tc_ok]
 unfold NGW_FactorWrite.write at write
 obtain ⟨v,hv,tail⟩ := AspisR1.Port3_PushFrame.bind_success _ _ _ write
 obtain ⟨p,hu,tail⟩ := AspisR1.Port3_PushFrame.bind_success _ _ _ tail
 rw [hv,bind_tc_ok]
 dsimp! only
 rw [hu,bind_tc_ok,hx,bind_tc_ok]
 cases Result.ok.inj tail
 rw [inner,bind_tc_ok]

#print axioms source
end NGW_CircleInitial
