import R1Z.PV_OptB_PathTuple
import R1Z.PV_OptB_AffineTuple
import R1Z.PV_OptB_AdmittedFamily
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_OptB_PathPoles
open R0P AspisR1.SpendRelation R1Z.BuilderSpendRelation
open R1J.SpendWitnessMap
abbrev M := R1J.SpendWitnessMap.F
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

def level (i : Fin 16) : Fin 24 := ⟨i.val+1,by omega⟩

def liftedWitness (w : Wspend) (t : Fin 16 → M) : Witness K :=
  BuilderCanonical.liftWitness (PV_OptB_WitnessFamily.witness w t)

def trace (pub : Public M) (w : Wspend) (t : Fin 16 → M) : Trace K :=
  R0Z.BuilderModel.buildModel (mapPub (PV_OptB_WitnessFamily.publicInput pub w t))
    (modelWitness (liftedWitness w t))

def base (w : Wspend) (i : Fin 16) (j : Fin 16) : K :=
  if h : j.val < 8 then ι ((w.path (level i)).2 ⟨j.val,h⟩) else 0

def phi (lam : K) (w : Wspend) (i : Fin 16) (z : M) : K :=
  PV_OptB_AffineTuple.value lam ((1124073538+3*(level i).val : Nat) : K)
    (base w i) (ι z)

theorem lifted_path (w : Wspend) (t : Fin 16 → M) (i : Fin 16) :
    (liftedWitness (K := K) w t).path (level i) =
      (false,fun j : Fin 8 => if j.val = 0 then ι (t i) else ι ((w.path (level i)).2 j)) := by
  have inside : 0 < (level i).val ∧ (level i).val ≤ 16 := by
    have := i.isLt
    dsimp [level]
    omega
  change ((PV_OptB_WitnessFamily.path w t (level i)).1,
    fun j => ι ((PV_OptB_WitnessFamily.path w t (level i)).2 j)) = _
  rw [PV_OptB_WitnessFamily.path,dif_pos inside]
  congr 1
  funext j
  by_cases zero : j.val = 0
  · simp only [zero,if_true]
    rfl
  · simp only [zero,if_false]

theorem tuple_value (pub : Public M) (w : Wspend) (t : Fin 16 → M) (lam : K) (i : Fin 16) :
    copyTupleValue lam (copyProducerTuple (trace pub w t) (PV_OptB_PathRegistry.rightLink (level i))) =
      phi lam w i (t i) := by
  have direction : ((liftedWitness (K := K) w t).path (level i)).1 = false := by
    rw [lifted_path]
  change copyTupleValue lam (copyProducerTuple
    (R0Z.BuilderModel.buildModel (mapPub (PV_OptB_WitnessFamily.publicInput pub w t))
      (modelWitness (liftedWitness w t))) _) = _
  rw [PV_OptB_PathTuple.tuple_shape _ _ _ direction]
  unfold phi PV_OptB_AffineTuple.value
  congr 2
  funext j
  rw [lifted_path]
  by_cases zero : j = 0
  · subst j
    rfl
  · have value_nonzero : j.val ≠ 0 := by intro hz; exact zero (Fin.ext hz)
    by_cases small : j.val < 8
    · simp only [small,dif_pos,value_nonzero,if_false,zero,base]
    · simp [base,small,zero]

theorem phi_injective (lam : K) (w : Wspend) (i : Fin 16) (nonzero : lam ≠ 0) :
    Function.Injective (phi lam w i) :=
  (PV_OptB_AffineTuple.injective lam _ _ nonzero).comp (ι : M →+* K).injective

theorem phi_mem (pub : Public M) (w : Wspend) (t : Fin 16 → M) (lam : K) (i : Fin 16) :
    phi lam w i (t i) ∈ PoleMassR1.poleSet (trace pub w t) lam := by
  rw [← tuple_value pub w t lam i]
  exact PV_OptB_PathRegistry.value_mem _ _ _

#print axioms lifted_path
#print axioms tuple_value
#print axioms phi_injective
#print axioms phi_mem
end R1Z.PV_OptB_PathPoles
