import NDO_JFw_TX2_P17
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_P18
open Aeneas Aeneas.Std Result JFw_TX2_PowersExplicit
def value : E := ⟨⟨⟨2090762636#u32,1506327751#u32⟩,⟨1519455049#u32,1311763271#u32⟩⟩,⟨⟨1622623315#u32,1039659929#u32⟩,⟨182058433#u32,1841500245#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((2090762636<2147483647 ∧ 1506327751<2147483647) ∧ (1519455049<2147483647 ∧ 1311763271<2147483647)) ∧
    ((1622623315<2147483647 ∧ 1039659929<2147483647) ∧ (182058433<2147483647 ∧ 1841500245<2147483647))
  omega
theorem lane0 : (-8981306011626863098 : ZMod 2147483647)=2090762636 := by decide
theorem lane1 : (18454059141104452284 : ZMod 2147483647)=1506327751 := by decide
theorem lane2 : (-2973084468009102225 : ZMod 2147483647)=1519455049 := by decide
theorem lane3 : (17324979169940113853 : ZMod 2147483647)=1311763271 := by decide
theorem lane4 : (-7506646916746103928 : ZMod 2147483647)=1622623315 := by decide
theorem lane5 : (20675169414799034752 : ZMod 2147483647)=1039659929 := by decide
theorem lane6 : (-1523684495412925515 : ZMod 2147483647)=182058433 := by decide
theorem lane7 : (10532488566807542587 : ZMod 2147483647)=1841500245 := by decide
theorem step : decode JFw_TX2_P17.value * decode gamma=decode value := by
  change (⟨⟨⟨947625749,1393554834⟩,⟨1221336616,1285347215⟩⟩,⟨⟨165443727,1487607774⟩,⟨1851765134,296259140⟩⟩⟩ : AspisWideTower.WideExact)*⟨⟨⟨855536485,461474173⟩,⟨798342634,1775607996⟩⟩,⟨⟨2127456138,1342862068⟩,⟨1305843559,1845381817⟩⟩⟩=⟨⟨⟨2090762636,1506327751⟩,⟨1519455049,1311763271⟩⟩,⟨⟨1622623315,1039659929⟩,⟨182058433,1841500245⟩⟩⟩
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
