import NDO_JFw_TX2_P15
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_P16
open Aeneas Aeneas.Std Result JFw_TX2_PowersExplicit
def value : E := ⟨⟨⟨1488821500#u32,1144228942#u32⟩,⟨2101769844#u32,468869550#u32⟩⟩,⟨⟨710351134#u32,1358018794#u32⟩,⟨480745599#u32,1884490624#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((1488821500<2147483647 ∧ 1144228942<2147483647) ∧ (2101769844<2147483647 ∧ 468869550<2147483647)) ∧
    ((710351134<2147483647 ∧ 1358018794<2147483647) ∧ (480745599<2147483647 ∧ 1884490624<2147483647))
  omega
theorem lane0 : (-12119171858383928784 : ZMod 2147483647)=1488821500 := by decide
theorem lane1 : (30474311265962330882 : ZMod 2147483647)=1144228942 := by decide
theorem lane2 : (-1116559286654986248 : ZMod 2147483647)=2101769844 := by decide
theorem lane3 : (20475671011657907472 : ZMod 2147483647)=468869550 := by decide
theorem lane4 : (-6551948230199771769 : ZMod 2147483647)=710351134 := by decide
theorem lane5 : (25082853959630148437 : ZMod 2147483647)=1358018794 := by decide
theorem lane6 : (1618217761303787401 : ZMod 2147483647)=480745599 := by decide
theorem lane7 : (17491907268429713797 : ZMod 2147483647)=1884490624 := by decide
theorem step : decode JFw_TX2_P15.value * decode gamma=decode value := by
  change (⟨⟨⟨2002812837,1496182417⟩,⟨1984673415,1484932522⟩⟩,⟨⟨1919977198,1583134462⟩,⟨1393716461,820218084⟩⟩⟩ : AspisWideTower.WideExact)*⟨⟨⟨855536485,461474173⟩,⟨798342634,1775607996⟩⟩,⟨⟨2127456138,1342862068⟩,⟨1305843559,1845381817⟩⟩⟩=⟨⟨⟨1488821500,1144228942⟩,⟨2101769844,468869550⟩⟩,⟨⟨710351134,1358018794⟩,⟨480745599,1884490624⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU, AspisV8R15.ExactTowerBase.qm31R, AspisV8R15.ExactTowerBase.M31Exact, AspisV8R15.ExactTowerBase.P]
  · exact lane0
  · exact lane1
  · exact lane2
  · exact lane3
  · exact lane4
  · exact lane5
  · exact lane6
  · exact lane7
theorem meaning : decode value=decode gamma^16 := by
  rw [show 16=(15:Nat)+1 from rfl,pow_succ,← JFw_TX2_P15.meaning]
  exact step.symm
theorem source : entry 16=value := identify 16 value canonical meaning
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
end AspisR1.JFw_TX2_P16
end
