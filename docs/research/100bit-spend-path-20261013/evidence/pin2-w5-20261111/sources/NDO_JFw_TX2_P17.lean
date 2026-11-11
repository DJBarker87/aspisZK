import NDO_JFw_TX2_P16
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_P17
open Aeneas Aeneas.Std Result JFw_TX2_PowersExplicit
def value : E := ⟨⟨⟨947625749#u32,1393554834#u32⟩,⟨1221336616#u32,1285347215#u32⟩⟩,⟨⟨165443727#u32,1487607774#u32⟩,⟨1851765134#u32,296259140#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((947625749<2147483647 ∧ 1393554834<2147483647) ∧ (1221336616<2147483647 ∧ 1285347215<2147483647)) ∧
    ((165443727<2147483647 ∧ 1487607774<2147483647) ∧ (1851765134<2147483647 ∧ 296259140<2147483647))
  omega
theorem lane0 : (-15581299392803280490 : ZMod 2147483647)=947625749 := by decide
theorem lane1 : (23115511147318108088 : ZMod 2147483647)=1393554834 := by decide
theorem lane2 : (-8621395336023846675 : ZMod 2147483647)=1221336616 := by decide
theorem lane3 : (12617318699245332105 : ZMod 2147483647)=1285347215 := by decide
theorem lane4 : (-7402976848791615230 : ZMod 2147483647)=165443727 := by decide
theorem lane5 : (18538090637901826412 : ZMod 2147483647)=1487607774 := by decide
theorem lane6 : (1371870917718439653 : ZMod 2147483647)=1851765134 := by decide
theorem lane7 : (12241086136749287497 : ZMod 2147483647)=296259140 := by decide
theorem step : decode JFw_TX2_P16.value * decode gamma=decode value := by
  change (⟨⟨⟨1488821500,1144228942⟩,⟨2101769844,468869550⟩⟩,⟨⟨710351134,1358018794⟩,⟨480745599,1884490624⟩⟩⟩ : AspisWideTower.WideExact)*⟨⟨⟨855536485,461474173⟩,⟨798342634,1775607996⟩⟩,⟨⟨2127456138,1342862068⟩,⟨1305843559,1845381817⟩⟩⟩=⟨⟨⟨947625749,1393554834⟩,⟨1221336616,1285347215⟩⟩,⟨⟨165443727,1487607774⟩,⟨1851765134,296259140⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU, AspisV8R15.ExactTowerBase.qm31R, AspisV8R15.ExactTowerBase.M31Exact, AspisV8R15.ExactTowerBase.P]
  · exact lane0
  · exact lane1
  · exact lane2
  · exact lane3
  · exact lane4
  · exact lane5
  · exact lane6
  · exact lane7
theorem meaning : decode value=decode gamma^17 := by
  rw [show 17=(16:Nat)+1 from rfl,pow_succ,← JFw_TX2_P16.meaning]
  exact step.symm
theorem source : entry 17=value := identify 17 value canonical meaning
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
end AspisR1.JFw_TX2_P17
end
