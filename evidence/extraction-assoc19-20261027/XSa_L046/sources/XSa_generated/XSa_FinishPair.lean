import XSa_FinishFour
import XSa_DotControl
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XSa_DotCarriers
set_option autoImplicit false
namespace XSa_FinishPair
open AspisR1ClaimPreparedBridge AspisR1EbyKFinish.Proof

def finish (a b : Dot) : Result C.E := do
 let lo ← XRn_Join_dotFinish a
 let hi ← XRn_Join_dotFinish b
 ok ⟨cq lo,cq hi⟩

theorem paired (a b : Dot) (count : Usize) :
 ∃ out, finish a b=ok out ∧ XRy_WideMultiply.Canonical out ∧
 ops.finishDot (state a b count)=ok (toClaimE out) := by
 rcases a with ⟨sums⟩
 rcases b with ⟨sums'⟩
 obtain ⟨s0,s1,s2,s3,hs⟩ := List.length_eq_four.mp sums.property
 obtain ⟨s4,s5,s6,s7,ht⟩ := List.length_eq_four.mp sums'.property
 have hs' : sums=Array.make 4#usize [s0,s1,s2,s3] := Subtype.ext hs
 have ht' : sums'=Array.make 4#usize [s4,s5,s6,s7] := Subtype.ext ht
 subst sums
 subst sums'
 let out : C.E := ⟨cq (XRn_Join_q [word s0,word s1,word s2,word s3]),
   cq (XRn_Join_q [word s4,word s5,word s6,word s7])⟩
 refine ⟨out,?_,?_,?_⟩
 · simp only [finish,XSa_FinishFour.four,bind_tc_ok]
   rfl
 · exact ⟨⟨⟨word_canonical s0,word_canonical s1⟩,⟨word_canonical s2,word_canonical s3⟩⟩,
     ⟨⟨word_canonical s4,word_canonical s5⟩,⟨word_canonical s6,word_canonical s7⟩⟩⟩
 · change (do
     let value ← AspisR1FinishDotSourceABI.finishFromPush (state _ _ count)
     ok (AspisR1CurrentPreparedClaim.ClaimParser.fromFinish value)) = _
   unfold AspisR1FinishDotSourceABI.finishFromPush AspisR1FinishDotSourceABI.toFinishState state
   rw [finish_eight,bind_tc_ok]
   rfl

#print axioms paired
end XSa_FinishPair
