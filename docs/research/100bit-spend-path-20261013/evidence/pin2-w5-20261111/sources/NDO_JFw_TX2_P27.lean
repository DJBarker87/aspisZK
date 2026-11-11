import NDO_JFw_TX2_P26
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_P27
open Aeneas Aeneas.Std Result JFw_TX2_PowersExplicit
def value : E := ⟨⟨⟨476910301#u32,1477068078#u32⟩,⟨1284387695#u32,977602599#u32⟩⟩,⟨⟨1686214252#u32,1757260182#u32⟩,⟨556660887#u32,1234719231#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((476910301<2147483647 ∧ 1477068078<2147483647) ∧ (1284387695<2147483647 ∧ 977602599<2147483647)) ∧
    ((1686214252<2147483647 ∧ 1757260182<2147483647) ∧ (556660887<2147483647 ∧ 1234719231<2147483647))
  omega
theorem lane0 : (-509830031265783222 : ZMod 2147483647)=476910301 := by decide
theorem lane1 : (20112310620610606404 : ZMod 2147483647)=1477068078 := by decide
theorem lane2 : (-357886785667390539 : ZMod 2147483647)=1284387695 := by decide
theorem lane3 : (14905473008831252143 : ZMod 2147483647)=977602599 := by decide
theorem lane4 : (-2221615824485278190 : ZMod 2147483647)=1686214252 := by decide
theorem lane5 : (14856381748188854426 : ZMod 2147483647)=1757260182 := by decide
theorem lane6 : (1057583667470361371 : ZMod 2147483647)=556660887 := by decide
theorem lane7 : (8889839940487755095 : ZMod 2147483647)=1234719231 := by decide
theorem step : decode JFw_TX2_P26.value * decode gamma=decode value := by
  change (⟨⟨⟨1081127453,1223560779⟩,⟨492705188,302580972⟩⟩,⟨⟨1322442357,534886635⟩,⟨1640616452,536904083⟩⟩⟩ : AspisWideTower.WideExact)*⟨⟨⟨855536485,461474173⟩,⟨798342634,1775607996⟩⟩,⟨⟨2127456138,1342862068⟩,⟨1305843559,1845381817⟩⟩⟩=⟨⟨⟨476910301,1477068078⟩,⟨1284387695,977602599⟩⟩,⟨⟨1686214252,1757260182⟩,⟨556660887,1234719231⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU, AspisV8R15.ExactTowerBase.qm31R, AspisV8R15.ExactTowerBase.M31Exact, AspisV8R15.ExactTowerBase.P]
  · exact lane0
  · exact lane1
  · exact lane2
  · exact lane3
  · exact lane4
  · exact lane5
  · exact lane6
  · exact lane7
theorem meaning : decode value=decode gamma^27 := by
  rw [show 27=(26:Nat)+1 from rfl,pow_succ,← JFw_TX2_P26.meaning]
  exact step.symm
theorem source : entry 27=value := identify 27 value canonical meaning
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
end AspisR1.JFw_TX2_P27
end
