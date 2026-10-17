import R0P.Copy

/-! Symbolic recurrence of the already retained iterative Copy powers.
The loop proof uses this recurrence directly, never a concrete power. -/
set_option autoImplicit false
namespace AspisR1.CopyPatternPowerModel
variable {K : Type} [Field K]

def powerAt (lambda : K) (limb : Nat) : K :=
  (List.range limb).foldl (fun power _ => power * lambda) lambda

theorem powerAt_zero (lambda : K) : powerAt lambda 0 = lambda := by rfl

theorem powerAt_succ (lambda : K) (limb : Nat) :
    powerAt lambda (limb + 1) = powerAt lambda limb * lambda := by
  unfold powerAt
  rw [List.range_succ, List.foldl_append]
  rfl

theorem retained_copyPowers (lambda : K) (limb : Fin 16) :
    R0P.copyPowers lambda limb = powerAt lambda limb.val := by rfl

#print axioms powerAt_zero
#print axioms powerAt_succ
#print axioms retained_copyPowers
end AspisR1.CopyPatternPowerModel
