import R1Z.SimCostView
set_option autoImplicit false
noncomputable section
namespace R1Z.SimCostShift6
open R0Z.HonestView R1Z.Batched Polynomial
attribute [local instance] Classical.propDecidable
abbrev c0 : PayloadCell R1Bat := .semanticCoeff 9 0
abbrev c1 : PayloadCell R1Bat := .semanticCoeff 9 1

/-- Symbolic sparsity, independent of the 30,671,382-cell enumeration. -/
theorem dir_cell {K : Type} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod AspisCircleGroupOrder.P) K] [BatchedLayer K R1Bat] (c : PayloadCell R1Bat) :
    R0Z.Shift.dir (K := K) c =
      if c = c0 then -(1/2 : K) else if c = c1 then 1 else 0 := by
  cases c with
  | semanticCoeff j i =>
    rw [R0Z.Shift.dir, R0Z.Shift.roundInclusion_semanticCoeff]
    by_cases hj : j = 9
    · subst j
      simp only [if_true, coeff_sub, coeff_X, coeff_C]
      by_cases hi0 : i = 0
      · subst i; simp [c0, c1]
      · by_cases hi1 : i = 1
        · subst i; simp [c0, c1]
        · have hv0 : i.val ≠ 0 := fun h => hi0 (Fin.ext h)
          have hv1 : i.val ≠ 1 := fun h => hi1 (Fin.ext h)
          simp [c0, c1, hi0, hi1, hv0, hv1, Ne.symm hv1]
    · simp [hj, c0, c1]
  | maskSum => rfl
  | pointClaim j i => rfl
  | extraClaim i => rfl
  | ood j i => rfl
  | inactiveSum => rfl
  | opened q s i => rfl
  | bat i => rfl

theorem update_value {K : Type} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod AspisCircleGroupOrder.P) K] [BatchedLayer K R1Bat]
    (v : Payload K R1Bat) (k : K) :
    Function.update (Function.update v c0 (v c0+k*(-(1/2)))) c1 (v c1+k) =
      v + k • R0Z.Shift.dir := by
  funext c
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, dir_cell]
  by_cases h0 : c = c0
  · subst c; simp [c0, c1]
  · by_cases h1 : c = c1
    · subst c; simp [c0, c1]
    · simp [Function.update_of_ne h0, Function.update_of_ne h1, h0, h1]

open R1Z.SimCostWriter
section Implementation
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod AspisCircleGroupOrder.P) K] [BatchedLayer K R1Bat]
    {A M I : Nat}
    (add : Stage (fun p : K × K => p.1+p.2) A)
    (mul : Stage (fun p : K × K => p.1*p.2) M)
    (inv : Stage (fun z : K => z⁻¹) I)

def updateRun (v : Payload K R1Bat) (k : K) : Costed (Payload K R1Bat) :=
  bind (mul.run (k,-(1/2))) fun delta =>
  bind (add.run (v c0,delta)) fun a =>
  bind (add.run (v c1,k)) fun b =>
    (Function.update (Function.update v c0 a) c1 b,4)

theorem updateRun_erase (v : Payload K R1Bat) (k : K) :
    (updateRun add mul v k).1 = v + k • R0Z.Shift.dir := by
  simp only [updateRun, erase_bind, mul.erase, add.erase]
  exact update_value v k

theorem updateRun_bound (v : Payload K R1Bat) (k : K) :
    (updateRun add mul v k).2 ≤ M+2*A+4 := by
  have hm := mul.bound (k,-(1/2))
  have ha := add.bound (v c0,(mul.run (k,-(1/2))).1)
  have hb := add.bound (v c1,k)
  simp only [updateRun, cost_bind]
  omega

def suffixRun (a original : K) (v : Payload K R1Bat) :=
  bind (add.run (a,-(1/2))) fun denominator =>
  bind (inv.run denominator) fun inverse =>
  bind (mul.run (original,inverse)) fun k => updateRun add mul v k

theorem suffixRun_erase (a original : K) (v : Payload K R1Bat) :
    (suffixRun add mul inv a original v).1 =
      v + (original * (a-1/2)⁻¹) • R0Z.Shift.dir := by
  simp only [suffixRun, erase_bind, add.erase, inv.erase, mul.erase,
    updateRun_erase, sub_eq_add_neg]

theorem suffixRun_bound (a original : K) (v : Payload K R1Bat) :
    (suffixRun add mul inv a original v).2 ≤ 3*A+2*M+I+4 := by
  have ha := add.bound (a,-(1/2))
  have hi := inv.bound (add.run (a,-(1/2))).1
  have hm := mul.bound (original,(inv.run (add.run (a,-(1/2))).1).1)
  have hu := updateRun_bound add mul v
    (mul.run (original,(inv.run (add.run (a,-(1/2))).1).1)).1
  simp only [suffixRun, cost_bind]
  omega

theorem suffixRun_shift {F : Subfield K} (pub : R0P.Public K)
    (B : R0P.PackBasis F) (ch : Challenges K) (v : Payload K R1Bat) :
    (suffixRun add mul inv (alpha ch 9) (R0Z.Shift.originalOf pub B ch v) v).1 =
      R0Z.Shift.shift pub B ch v :=
  suffixRun_erase add mul inv _ _ _
end Implementation

#print axioms dir_cell
#print axioms update_value
#print axioms updateRun_erase
#print axioms updateRun_bound
#print axioms suffixRun_erase
#print axioms suffixRun_bound
#print axioms suffixRun_shift
end R1Z.SimCostShift6
