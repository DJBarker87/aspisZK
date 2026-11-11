import NDO_JFw_TX2_P03
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_P04
open Aeneas Aeneas.Std Result JFw_TX2_PowersExplicit
def value : E := ⟨⟨⟨46530699#u32,1176229749#u32⟩,⟨1759211712#u32,1927035533#u32⟩⟩,⟨⟨258016984#u32,720994932#u32⟩,⟨1637998205#u32,1813172101#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((46530699<2147483647 ∧ 1176229749<2147483647) ∧ (1759211712<2147483647 ∧ 1927035533<2147483647)) ∧
    ((258016984<2147483647 ∧ 720994932<2147483647) ∧ (1637998205<2147483647 ∧ 1813172101<2147483647))
  omega
theorem lane0 : (-7263481785137224461 : ZMod 2147483647)=46530699 := by decide
theorem lane1 : (19463544364463229565 : ZMod 2147483647)=1176229749 := by decide
theorem lane2 : (-7335390337768847858 : ZMod 2147483647)=1759211712 := by decide
theorem lane3 : (15659198003468234574 : ZMod 2147483647)=1927035533 := by decide
theorem lane4 : (-6322792771826537497 : ZMod 2147483647)=258016984 := by decide
theorem lane5 : (16199004567107315913 : ZMod 2147483647)=720994932 := by decide
theorem lane6 : (-2193005855534736152 : ZMod 2147483647)=1637998205 := by decide
theorem lane7 : (8152304143693591722 : ZMod 2147483647)=1813172101 := by decide
theorem step : decode JFw_TX2_P03.value * decode gamma=decode value := by
  change (⟨⟨⟨658110426,1790040855⟩,⟨598652022,49316637⟩⟩,⟨⟨503185052,1277459006⟩,⟨1692452649,1165546036⟩⟩⟩ : AspisWideTower.WideExact)*⟨⟨⟨855536485,461474173⟩,⟨798342634,1775607996⟩⟩,⟨⟨2127456138,1342862068⟩,⟨1305843559,1845381817⟩⟩⟩=⟨⟨⟨46530699,1176229749⟩,⟨1759211712,1927035533⟩⟩,⟨⟨258016984,720994932⟩,⟨1637998205,1813172101⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU, AspisV8R15.ExactTowerBase.qm31R, AspisV8R15.ExactTowerBase.M31Exact, AspisV8R15.ExactTowerBase.P]
  · exact lane0
  · exact lane1
  · exact lane2
  · exact lane3
  · exact lane4
  · exact lane5
  · exact lane6
  · exact lane7
theorem meaning : decode value=decode gamma^4 := by
  rw [show 4=(3:Nat)+1 from rfl,pow_succ,← JFw_TX2_P03.meaning]
  exact step.symm
theorem source : entry 4=value := identify 4 value canonical meaning
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
end AspisR1.JFw_TX2_P04
end
