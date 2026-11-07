import NNH_ThreeAccounts
import NNH_Stage1BodyChild
set_option autoImplicit false
noncomputable section
namespace NNH_Stage1TopCut
open RSL NNH_Libraries

theorem produce (a : TX1_345.Args) (saved : Bytes) (env : Env)
 (success : NNH_ReturnsBundle.tx1Value a env=.ok saved) :
 ∃ p pub ck,a.accounts=[p,pub,ck] ∧ TX1_345.badRoute a=false ∧
 Nonempty (NNH_Stage1Cut.Packet a p pub ck saved env) := by
 change NNH_Stage1RefEval.value VL P NNH_Tx1Returns.values C a env=.ok saved at success
 cases route : TX1_345.badRoute a with
 | true => simp only [NNH_Stage1RefEval.value,route,if_true] at success; cases success
 | false =>
  have flags:=route
  unfold TX1_345.badRoute at flags
  have count : a.accounts.length=3 := by
   have both := Bool.or_eq_false_iff.mp flags
   exact bne_eq_false_iff_eq.mp both.2
  obtain ⟨p,pub,ck,shape⟩ := NNH_ThreeAccounts.shape a.accounts count
  simp only [NNH_Stage1RefEval.value,route,if_false,shape] at success
  exact ⟨p,pub,ck,shape,rfl,NNH_Stage1Cut.produce a p pub ck saved env success⟩
#print axioms produce
end NNH_Stage1TopCut
