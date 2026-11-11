import NDO_JFw_TX2_P11
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_P12
open Aeneas Aeneas.Std Result JFw_TX2_PowersExplicit
def value : E := ⟨⟨⟨165022405#u32,1151288564#u32⟩,⟨1187929565#u32,975586913#u32⟩⟩,⟨⟨1580123087#u32,208006299#u32⟩,⟨605264612#u32,565298516#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((165022405<2147483647 ∧ 1151288564<2147483647) ∧ (1187929565<2147483647 ∧ 975586913<2147483647)) ∧
    ((1580123087<2147483647 ∧ 208006299<2147483647) ∧ (605264612<2147483647 ∧ 565298516<2147483647))
  omega
theorem lane0 : (-18245876912142234740 : ZMod 2147483647)=165022405 := by decide
theorem lane1 : (28154424084145245660 : ZMod 2147483647)=1151288564 := by decide
theorem lane2 : (-9223117204519874986 : ZMod 2147483647)=1187929565 := by decide
theorem lane3 : (17973564618064816840 : ZMod 2147483647)=975586913 := by decide
theorem lane4 : (-10669116820242340285 : ZMod 2147483647)=1580123087 := by decide
theorem lane5 : (19892138157625821201 : ZMod 2147483647)=208006299 := by decide
theorem lane6 : (-1288031586019467597 : ZMod 2147483647)=605264612 := by decide
theorem lane7 : (16675110650793294781 : ZMod 2147483647)=565298516 := by decide
theorem step : decode JFw_TX2_P11.value * decode gamma=decode value := by
  change (⟨⟨⟨1945421184,1962418097⟩,⟨1393751537,1006861821⟩⟩,⟨⟨1733815124,1668087661⟩,⟨805386676,2018426674⟩⟩⟩ : AspisWideTower.WideExact)*⟨⟨⟨855536485,461474173⟩,⟨798342634,1775607996⟩⟩,⟨⟨2127456138,1342862068⟩,⟨1305843559,1845381817⟩⟩⟩=⟨⟨⟨165022405,1151288564⟩,⟨1187929565,975586913⟩⟩,⟨⟨1580123087,208006299⟩,⟨605264612,565298516⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU, AspisV8R15.ExactTowerBase.qm31R, AspisV8R15.ExactTowerBase.M31Exact, AspisV8R15.ExactTowerBase.P]
  · exact lane0
  · exact lane1
  · exact lane2
  · exact lane3
  · exact lane4
  · exact lane5
  · exact lane6
  · exact lane7
theorem meaning : decode value=decode gamma^12 := by
  rw [show 12=(11:Nat)+1 from rfl,pow_succ,← JFw_TX2_P11.meaning]
  exact step.symm
theorem source : entry 12=value := identify 12 value canonical meaning
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
end AspisR1.JFw_TX2_P12
end
