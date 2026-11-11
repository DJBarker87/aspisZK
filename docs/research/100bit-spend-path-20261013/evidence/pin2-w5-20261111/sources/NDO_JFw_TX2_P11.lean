import NDO_JFw_TX2_P10
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_P11
open Aeneas Aeneas.Std Result JFw_TX2_PowersExplicit
def value : E := ⟨⟨⟨1945421184#u32,1962418097#u32⟩,⟨1393751537#u32,1006861821#u32⟩⟩,⟨⟨1733815124#u32,1668087661#u32⟩,⟨805386676#u32,2018426674#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((1945421184<2147483647 ∧ 1962418097<2147483647) ∧ (1393751537<2147483647 ∧ 1006861821<2147483647)) ∧
    ((1733815124<2147483647 ∧ 1668087661<2147483647) ∧ (805386676<2147483647 ∧ 2018426674<2147483647))
  omega
theorem lane0 : (-7603805654355996820 : ZMod 2147483647)=1945421184 := by decide
theorem lane1 : (13363887917320895788 : ZMod 2147483647)=1962418097 := by decide
theorem lane2 : (-3119646730939178421 : ZMod 2147483647)=1393751537 := by decide
theorem lane3 : (10264693532671112503 : ZMod 2147483647)=1006861821 := by decide
theorem lane4 : (-6776247351302681225 : ZMod 2147483647)=1733815124 := by decide
theorem lane5 : (13219967598126398065 : ZMod 2147483647)=1668087661 := by decide
theorem lane6 : (-4288481875400804148 : ZMod 2147483647)=805386676 := by decide
theorem lane7 : (8085244867474989172 : ZMod 2147483647)=2018426674 := by decide
theorem step : decode JFw_TX2_P10.value * decode gamma=decode value := by
  change (⟨⟨⟨1406118,2097040101⟩,⟨648438797,831220367⟩⟩,⟨⟨775089091,1112063832⟩,⟨823850592,71121305⟩⟩⟩ : AspisWideTower.WideExact)*⟨⟨⟨855536485,461474173⟩,⟨798342634,1775607996⟩⟩,⟨⟨2127456138,1342862068⟩,⟨1305843559,1845381817⟩⟩⟩=⟨⟨⟨1945421184,1962418097⟩,⟨1393751537,1006861821⟩⟩,⟨⟨1733815124,1668087661⟩,⟨805386676,2018426674⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU, AspisV8R15.ExactTowerBase.qm31R, AspisV8R15.ExactTowerBase.M31Exact, AspisV8R15.ExactTowerBase.P]
  · exact lane0
  · exact lane1
  · exact lane2
  · exact lane3
  · exact lane4
  · exact lane5
  · exact lane6
  · exact lane7
theorem meaning : decode value=decode gamma^11 := by
  rw [show 11=(10:Nat)+1 from rfl,pow_succ,← JFw_TX2_P10.meaning]
  exact step.symm
theorem source : entry 11=value := identify 11 value canonical meaning
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
end AspisR1.JFw_TX2_P11
end
