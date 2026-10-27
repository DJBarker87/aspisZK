import R1D18PointWeights
import FJc_WeightConstants
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJd_PointReference
variable {K : Type} [Field K]
/-- Four entries emitted by the constructor, in the shipped order. -/
def factors (a b : K) (s : Fin 4) : K :=
  match s.val with
  | 0 => (1-a)*(1-b)
  | 1 => a*(1-b)
  | 2 => (1-a)*b
  | _ => a*b

theorem factor_value (a b : K) (s : Fin 4) :
    factors a b s=pairFactor a b s.val := by
  fin_cases s <;> simp [factors,pairFactor]

def coordinateA (p : Fin 10 → K) (d : Fin 5) : K :=
  p ⟨9-2*(d18Tau d).val,by have := (d18Tau d).isLt; omega⟩
def coordinateB (p : Fin 10 → K) (d : Fin 5) : K :=
  p ⟨8-2*(d18Tau d).val,by have := (d18Tau d).isLt; omega⟩
def pointFactors (p : Fin 10 → K) (d : Fin 5) (s : Fin 4) : K :=
  factors (coordinateA p d) (coordinateB p d) s

def tensor (f : Fin 5 → Fin 4 → K) (j : Fin 1024) : K :=
  ∏ d : Fin 5, f d ⟨j.val/4^d.val%4,Nat.mod_lt _ (by omega)⟩

/-- Closed-form reference meaning. This is not the installed loop bridge. -/
theorem original (p : Fin 10 → K) (j : Fin 1024) :
    tensor (pointFactors p) j=tensorPoint p j := by
  unfold tensor tensorPoint
  apply Finset.prod_congr rfl
  intro d _
  exact factor_value (coordinateA p d) (coordinateB p d) _
#print axioms factor_value
#print axioms original
end AspisR1.FJd_PointReference
end
