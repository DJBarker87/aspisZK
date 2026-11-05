import NHS_VecLengths
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHS_FoldDomain
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
/-- The source vector extensions determine S4's length without re-proving
or importing an obsolete ownership forest's byte-value theorem. -/
theorem length (v : verifier.View) (tail : v.round1.val.length=224)
 (payload : Slice U8) (call : NHL_PreparedOpening.foldPayload v=ok payload) :
 payload.val.length=256 := by
 unfold NHL_PreparedOpening.foldPayload at call
 have add : (32#usize+224#usize : Result Usize)=ok 256#usize := rfl
 rw [add,bind_tc_ok] at call
 obtain ⟨root,_,call⟩ := NFW_Invert.bind _ _ _ call
 simp only [lift,bind_tc_ok] at call
 obtain ⟨b1,first,call⟩ := NFW_Invert.bind _ _ _ call
 obtain ⟨b2,second,last⟩ := NFW_Invert.bind _ _ _ call
 have same := Result.ok.inj last
 subst payload
 have l1 := NHS_VecLengths.extend_length _ _ _ _ first
 have l2 := NHS_VecLengths.extend_length _ _ _ _ second
 have size := root.property
 change root.val.length=32 at size
 change b1.val.length=0+root.val.length at l1
 change b2.val.length=256
 change b2.val.length=b1.val.length+v.round1.val.length at l2
 omega

theorem bound (v : verifier.View) (tail : v.round1.val.length=224)
 (payload : Slice U8) (call : NHL_PreparedOpening.foldPayload v=ok payload) :
 payload.val.length≤2048 := by
 rw [length v tail payload call]
 decide
#print axioms length
#print axioms bound
end AspisR1.NHS_FoldDomain
