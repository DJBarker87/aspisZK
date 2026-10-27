import RPu_FJn_FormulaMap
import RPu_FJn_LaneModel
set_option autoImplicit false
namespace AspisR1.FJn_TerminalFormulaModel
abbrev E:=AspisWideTower.WideExact
def openings (y : Fin 3 → Fin 29 → E) : R0P.Openings E :=
  ⟨fun i=>y 0 (Fin.castLE (by omega) i),fun i=>y 1 (Fin.castLE (by omega) i),
   fun i=>y 2 (Fin.castLE (by omega) i)⟩
attribute [local irreducible] R0P.SemSource.laneAt R0P.SemSource.eqValue R0P.SemSource.selAt
  R0P.SemSource.activeAt openings
/-- Pure terminal formula assembly, isolated from concrete native carriers. -/
theorem value (p : R0P.Public E) (lambda chi theta mu : E) (zc point : Fin 10 → E)
    (y : Fin 3 → Fin 29 → E) (comp h active : E)
    (hc : comp=∑ i : Fin 29,theta^i.val*R0P.SemSource.laneAt p lambda chi ConcretePackBasis.basis
      (openings y) h (R0P.SemSource.selAt point) i)
    (hh : h=y 0 26) (ha : active=R0P.SemSource.activeAt point) :
    FJn_FormulaMap.formula (R0P.SemSource.eqValue zc point) comp mu h active=
      R0P.SemSource.terminalValue p lambda chi theta mu zc ConcretePackBasis.basis y point := by
  rw [hc,hh,ha]
  unfold FJn_FormulaMap.formula R0P.SemSource.terminalValue openings
  ring
#print axioms value
end AspisR1.FJn_TerminalFormulaModel
