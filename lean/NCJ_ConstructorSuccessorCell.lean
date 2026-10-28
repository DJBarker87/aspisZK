import NCJ_ConstructorQM
import NCJ_ConstructorArrays
import NCJ_Reverse
set_option autoImplicit false
namespace NCJ_ConstructorSuccessorCell
open Aeneas Aeneas.Std Result ControlFlow NCJ_ConstructorQM
open NCJ_ConstructorArrays (Holds)

theorem source (z successor : Array Q 10#usize) (carry : Q)
    (hz : Holds Canon z) (hs : Holds Canon successor) (hc : Canon carry)
    (iter cursor : NCJ_Reverse.Rev) (coordinate : Usize) (bound : coordinate.val<10)
    (advance : NCJ_Reverse.next iter=ok (some coordinate,cursor)) :
    ∃ out next,FIn_WeightsExtract.state_only_prefix.state_only_statement_points_loop.body z iter successor carry=
      ok (cont (cursor,out,next)) ∧ Holds Canon out ∧ Canon next := by
  let bit := NCJ_GuardExact.pick z coordinate.val bound
  have read := NCJ_GuardExact.index z coordinate bound
  change Array.index_usize z coordinate=ok bit at read
  have cb := NCJ_ConstructorArrays.canonical_pick Canon z coordinate.val bound hz
  obtain ⟨product,hm,cm⟩ := mul bit carry cb hc
  obtain ⟨sum,ha,ca⟩ := add bit carry cb hc
  obtain ⟨twice,hd,cd⟩ := add product product cm cm
  obtain ⟨value,hv,cv⟩ := sub sum twice ca cd
  let out := NCJ_ConstructorArrays.put successor coordinate.val value
  have update := NCJ_ConstructorArrays.update successor coordinate value bound
  change Array.update successor coordinate value=ok out at update
  refine ⟨out,product,?_,NCJ_ConstructorArrays.canonical_put Canon successor coordinate.val value hs cv,cm⟩
  unfold NCJ_Reverse.next at advance
  unfold FIn_WeightsExtract.state_only_prefix.state_only_statement_points_loop.body
  rw [advance]
  simp only [bind_tc_ok]
  dsimp! only
  simp only [read,hm,ha,hd,hv,update,bind_tc_ok]

#print axioms source
end NCJ_ConstructorSuccessorCell
