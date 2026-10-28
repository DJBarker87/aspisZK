import NDO_JFw_TX2_P17
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_P18
open Aeneas Aeneas.Std Result JFw_TX2_PowersExplicit
def value : E := ⟨⟨⟨1298953245#u32,1504805752#u32⟩,⟨2073609211#u32,1840812326#u32⟩⟩,⟨⟨1755193245#u32,1295624230#u32⟩,⟨476103426#u32,940478841#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((1298953245<2147483647 ∧ 1504805752<2147483647) ∧ (2073609211<2147483647 ∧ 1840812326<2147483647)) ∧
    ((1755193245<2147483647 ∧ 1295624230<2147483647) ∧ (476103426<2147483647 ∧ 940478841<2147483647))
  omega
theorem lane0 : (-14441544909485650614 : ZMod 2147483647)=1298953245 := by decide
theorem lane1 : (21817443145656517007 : ZMod 2147483647)=1504805752 := by decide
theorem lane2 : (-6731218112841190807 : ZMod 2147483647)=2073609211 := by decide
theorem lane3 : (18019051238856294879 : ZMod 2147483647)=1840812326 := by decide
theorem lane4 : (-11919409113195176320 : ZMod 2147483647)=1755193245 := by decide
theorem lane5 : (19342151879283926739 : ZMod 2147483647)=1295624230 := by decide
theorem lane6 : (-2004217242836691728 : ZMod 2147483647)=476103426 := by decide
theorem lane7 : (13133123180472966544 : ZMod 2147483647)=940478841 := by decide
theorem step : decode JFw_TX2_P17.value * decode gamma=decode value := by
  change (⟨⟨⟨1003904973,1147694576⟩,⟨1474177753,1511477847⟩⟩,⟨⟨1335902916,995962325⟩,⟨94118806,2068940067⟩⟩⟩ : AspisWideTower.WideExact)*⟨⟨⟨855639275,1483149559⟩,⟨1898717401,1849775942⟩⟩,⟨⟨1112406525,1796814865⟩,⟨1838939499,418714188⟩⟩⟩=⟨⟨⟨1298953245,1504805752⟩,⟨2073609211,1840812326⟩⟩,⟨⟨1755193245,1295624230⟩,⟨476103426,940478841⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU, AspisV8R15.ExactTowerBase.qm31R, AspisV8R15.ExactTowerBase.M31Exact, AspisV8R15.ExactTowerBase.P]
  · exact lane0
  · exact lane1
  · exact lane2
  · exact lane3
  · exact lane4
  · exact lane5
  · exact lane6
  · exact lane7
theorem meaning : decode value=decode gamma^18 := by
  rw [show 18=(17:Nat)+1 from rfl,pow_succ,← JFw_TX2_P17.meaning]
  exact step.symm
theorem source : entry 18=value := identify 18 value canonical meaning
#print axioms canonical
#print axioms lane0
#print axioms lane1
#print axioms lane2
#print axioms lane3
#print axioms lane4
#print axioms lane5
#print axioms lane6
#print axioms lane7
#print axioms step
#print axioms meaning
#print axioms source
end AspisR1.JFw_TX2_P18
end
