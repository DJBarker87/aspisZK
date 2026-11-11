import NDO_JFw_TX2_P24
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_P25
open Aeneas Aeneas.Std Result JFw_TX2_PowersExplicit
def value : E := ⟨⟨⟨875085308#u32,526331536#u32⟩,⟨1793465312#u32,2138906138#u32⟩⟩,⟨⟨1321124323#u32,119982949#u32⟩,⟨1044440065#u32,867672856#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((875085308<2147483647 ∧ 526331536<2147483647) ∧ (1793465312<2147483647 ∧ 2138906138<2147483647)) ∧
    ((1321124323<2147483647 ∧ 119982949<2147483647) ∧ (1044440065<2147483647 ∧ 867672856<2147483647))
  omega
theorem lane0 : (-9500528974848454777 : ZMod 2147483647)=875085308 := by decide
theorem lane1 : (18329380216719350313 : ZMod 2147483647)=526331536 := by decide
theorem lane2 : (-3260627436384664925 : ZMod 2147483647)=1793465312 := by decide
theorem lane3 : (10363471513060391227 : ZMod 2147483647)=2138906138 := by decide
theorem lane4 : (-9867360307769339459 : ZMod 2147483647)=1321124323 := by decide
theorem lane5 : (12859093028513345901 : ZMod 2147483647)=119982949 := by decide
theorem lane6 : (-520057878981107769 : ZMod 2147483647)=1044440065 := by decide
theorem lane7 : (9977156521001987353 : ZMod 2147483647)=867672856 := by decide
theorem step : decode JFw_TX2_P24.value * decode gamma=decode value := by
  change (⟨⟨⟨391568943,1006575155⟩,⟨990907796,1343747376⟩⟩,⟨⟨1263573490,408284389⟩,⟨792956610,952882229⟩⟩⟩ : AspisWideTower.WideExact)*⟨⟨⟨855536485,461474173⟩,⟨798342634,1775607996⟩⟩,⟨⟨2127456138,1342862068⟩,⟨1305843559,1845381817⟩⟩⟩=⟨⟨⟨875085308,526331536⟩,⟨1793465312,2138906138⟩⟩,⟨⟨1321124323,119982949⟩,⟨1044440065,867672856⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU, AspisV8R15.ExactTowerBase.qm31R, AspisV8R15.ExactTowerBase.M31Exact, AspisV8R15.ExactTowerBase.P]
  · exact lane0
  · exact lane1
  · exact lane2
  · exact lane3
  · exact lane4
  · exact lane5
  · exact lane6
  · exact lane7
theorem meaning : decode value=decode gamma^25 := by
  rw [show 25=(24:Nat)+1 from rfl,pow_succ,← JFw_TX2_P24.meaning]
  exact step.symm
theorem source : entry 25=value := identify 25 value canonical meaning
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
end AspisR1.JFw_TX2_P25
end
