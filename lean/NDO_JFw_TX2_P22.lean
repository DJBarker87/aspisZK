import NDO_JFw_TX2_P21
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_P22
open Aeneas Aeneas.Std Result JFw_TX2_PowersExplicit
def value : E := ⟨⟨⟨1478307182#u32,1255280192#u32⟩,⟨1837870964#u32,1625323762#u32⟩⟩,⟨⟨1423042536#u32,1466877680#u32⟩,⟨1923715623#u32,522298462#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((1478307182<2147483647 ∧ 1255280192<2147483647) ∧ (1837870964<2147483647 ∧ 1625323762<2147483647)) ∧
    ((1423042536<2147483647 ∧ 1466877680<2147483647) ∧ (1923715623<2147483647 ∧ 522298462<2147483647))
  omega
theorem lane0 : (-2167218457596907304 : ZMod 2147483647)=1478307182 := by decide
theorem lane1 : (21450854866386718857 : ZMod 2147483647)=1255280192 := by decide
theorem lane2 : (-1724470055075788745 : ZMod 2147483647)=1837870964 := by decide
theorem lane3 : (14695403547789318554 : ZMod 2147483647)=1625323762 := by decide
theorem lane4 : (-2928992746182170962 : ZMod 2147483647)=1423042536 := by decide
theorem lane5 : (15376716505138111115 : ZMod 2147483647)=1466877680 := by decide
theorem lane6 : (985555531866228502 : ZMod 2147483647)=1923715623 := by decide
theorem lane7 : (12783855550648476307 : ZMod 2147483647)=522298462 := by decide
theorem step : decode JFw_TX2_P21.value * decode gamma=decode value := by
  change (⟨⟨⟨235809508,1485990146⟩,⟨1085624123,82870699⟩⟩,⟨⟨1751078325,1425322328⟩,⟨826458039,863066484⟩⟩⟩ : AspisWideTower.WideExact)*⟨⟨⟨855639275,1483149559⟩,⟨1898717401,1849775942⟩⟩,⟨⟨1112406525,1796814865⟩,⟨1838939499,418714188⟩⟩⟩=⟨⟨⟨1478307182,1255280192⟩,⟨1837870964,1625323762⟩⟩,⟨⟨1423042536,1466877680⟩,⟨1923715623,522298462⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU, AspisV8R15.ExactTowerBase.qm31R, AspisV8R15.ExactTowerBase.M31Exact, AspisV8R15.ExactTowerBase.P]
  · exact lane0
  · exact lane1
  · exact lane2
  · exact lane3
  · exact lane4
  · exact lane5
  · exact lane6
  · exact lane7
theorem meaning : decode value=decode gamma^22 := by
  rw [show 22=(21:Nat)+1 from rfl,pow_succ,← JFw_TX2_P21.meaning]
  exact step.symm
theorem source : entry 22=value := identify 22 value canonical meaning
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
end AspisR1.JFw_TX2_P22
end
