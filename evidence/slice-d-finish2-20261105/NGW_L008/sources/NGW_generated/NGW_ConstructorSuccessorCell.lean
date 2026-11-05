import NGW_ConstructorQM
import NGW_ConstructorArrays
import NGW_Reverse
set_option autoImplicit false
namespace NGW_ConstructorSuccessorCell
open Aeneas Aeneas.Std Result ControlFlow NGW_ConstructorQM
open NGW_ConstructorArrays (Holds)

theorem source (z successor : Array Q 10#usize) (carry : Q)
    (hz : Holds Canon z) (hs : Holds Canon successor) (hc : Canon carry)
    (iter cursor : NGW_Reverse.Rev) (coordinate : Usize) (bound : coordinate.val<10)
    (advance : NGW_Reverse.next iter=ok (some coordinate,cursor)) :
    ∃ out next,FIn_WeightsExtract.state_only_prefix.state_only_statement_points_loop.body z iter successor carry=
      ok (cont (cursor,out,next)) ∧ Holds Canon out ∧ Canon next := by
  let bit := NGM_GuardExact.pick z coordinate.val bound
  have read := NGM_GuardExact.index z coordinate bound
  change Array.index_usize z coordinate=ok bit at read
  have cb := NGW_ConstructorArrays.canonical_pick Canon z coordinate.val bound hz
  obtain ⟨product,hm,cm⟩ := mul bit carry cb hc
  obtain ⟨sum,ha,ca⟩ := add bit carry cb hc
  obtain ⟨twice,hd,cd⟩ := add product product cm cm
  obtain ⟨value,hv,cv⟩ := sub sum twice ca cd
  let out := NGW_ConstructorArrays.put successor coordinate.val value
  have update := NGW_ConstructorArrays.update successor coordinate value bound
  change Array.update successor coordinate value=ok out at update
  refine ⟨out,product,?_,NGW_ConstructorArrays.canonical_put Canon successor coordinate.val value hs cv,cm⟩
  unfold NGW_Reverse.next at advance
  unfold FIn_WeightsExtract.state_only_prefix.state_only_statement_points_loop.body
  rw [advance]
  simp only [bind_tc_ok]
  dsimp! only
  simp only [read,hm,ha,hd,hv,update,bind_tc_ok]

#print axioms source
end NGW_ConstructorSuccessorCell
