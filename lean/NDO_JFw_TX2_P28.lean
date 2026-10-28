import NDO_JFw_TX2_P27
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_P28
open Aeneas Aeneas.Std Result JFw_TX2_PowersExplicit
def value : E := ⟨⟨⟨2136659036#u32,1454808535#u32⟩,⟨901973532#u32,323718155#u32⟩⟩,⟨⟨447208057#u32,1244418415#u32⟩,⟨2052833682#u32,2086368445#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((2136659036<2147483647 ∧ 1454808535<2147483647) ∧ (901973532<2147483647 ∧ 323718155<2147483647)) ∧
    ((447208057<2147483647 ∧ 1244418415<2147483647) ∧ (2052833682<2147483647 ∧ 2086368445<2147483647))
  omega
theorem lane0 : (-9841896092260256493 : ZMod 2147483647)=2136659036 := by decide
theorem lane1 : (28913564726951371254 : ZMod 2147483647)=1454808535 := by decide
theorem lane2 : (214801934581547947 : ZMod 2147483647)=901973532 := by decide
theorem lane3 : (20783729872842146719 : ZMod 2147483647)=323718155 := by decide
theorem lane4 : (-7066466972773769466 : ZMod 2147483647)=447208057 := by decide
theorem lane5 : (25893781427864596321 : ZMod 2147483647)=1244418415 := by decide
theorem lane6 : (-664700075648304136 : ZMod 2147483647)=2052833682 := by decide
theorem lane7 : (15086440033091050028 : ZMod 2147483647)=2086368445 := by decide
theorem step : decode JFw_TX2_P27.value * decode gamma=decode value := by
  change (⟨⟨⟨509504871,562297437⟩,⟨830444110,750558315⟩⟩,⟨⟨1775007834,1847964904⟩,⟨2126955715,1829355625⟩⟩⟩ : AspisWideTower.WideExact)*⟨⟨⟨855639275,1483149559⟩,⟨1898717401,1849775942⟩⟩,⟨⟨1112406525,1796814865⟩,⟨1838939499,418714188⟩⟩⟩=⟨⟨⟨2136659036,1454808535⟩,⟨901973532,323718155⟩⟩,⟨⟨447208057,1244418415⟩,⟨2052833682,2086368445⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU, AspisV8R15.ExactTowerBase.qm31R, AspisV8R15.ExactTowerBase.M31Exact, AspisV8R15.ExactTowerBase.P]
  · exact lane0
  · exact lane1
  · exact lane2
  · exact lane3
  · exact lane4
  · exact lane5
  · exact lane6
  · exact lane7
theorem meaning : decode value=decode gamma^28 := by
  rw [show 28=(27:Nat)+1 from rfl,pow_succ,← JFw_TX2_P27.meaning]
  exact step.symm
theorem source : entry 28=value := identify 28 value canonical meaning
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
end AspisR1.JFw_TX2_P28
end
