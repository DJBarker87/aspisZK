import NNH_Stage1TopCut
set_option autoImplicit false
noncomputable section
namespace NNH_Tx1SuccessfulRoute
open RSL NNH_Libraries

theorem source (a : TX1_345.Args) (saved : Bytes) (env : Env)
 (success : NNH_ReturnsBundle.tx1Value a env=.ok saved) : a.data=[3,10] := by
 obtain ⟨p,pub,ck,shape,route,⟨packet⟩⟩ := NNH_Stage1TopCut.produce a saved env success
 obtain ⟨child⟩ := NNH_Stage1BodyChild.produce a p pub ck saved env packet
 have split:=child.split
 change (a.data.getD 1 0).toNat=SPLIT at split
 have flags:=route
 unfold TX1_345.badRoute at flags
 have routeFalse := (Bool.or_eq_false_iff.mp flags).1
 have allowed : a.data=[3,10] ∨ a.data=[3,11] := by
  have eqTrue : (a.data==[3,10] || a.data==[3,11])=true := by
   cases values : (a.data==[3,10] || a.data==[3,11]) with
   | true => rfl
   | false => rw [values] at routeFalse; cases routeFalse
  simpa only [Bool.or_eq_true,beq_iff_eq] using eqTrue
 rcases allowed with good | bad
 · exact good
 · rw [bad] at split
   cases split
#print axioms source
end NNH_Tx1SuccessfulRoute
