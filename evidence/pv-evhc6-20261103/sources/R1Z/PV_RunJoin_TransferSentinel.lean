import R1Z.PV_RunJoin_SentinelPermutation2

/-! Literal transfer-fixture sentinel, composed from bounded single-round
cells. No whole sponge/recurrence kernel reduction is used. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_TransferSentinel
open R0P PV_RunJoin_Sentinel PV_RunJoin_FixtureRecords

def middle : Fin 8 → Scalar := fun i =>
  if i.val = 0 then 400 else if i.val = 1 then 77 else digest 600 ⟨i.val-2,by omega⟩

def tail : Fin 8 → Scalar := fun i =>
  if h : i.val < 2 then digest 600 ⟨i.val+6,by omega⟩ else 0

theorem first_absorb : absorb (spongeInit 0x41530003 18) (digest 500) = s_0_0 := by
  funext i
  fin_cases i <;> rfl

theorem middle_absorb : absorb s_0_23 middle = s_1_0 := by
  funext i
  fin_cases i <;> rfl

theorem tail_absorb : absorb s_1_23 tail = s_2_0 := by
  funext i
  fin_cases i <;> rfl

theorem value : (fixturePublic false).change 7 = (351017421 : Scalar) := by
  change noteCommitment (digest 500) 400 77 (digest 600) 7 = _
  simp only [noteCommitment,spongeStep]
  change digestOf (poseidonPermutation (absorb
    (poseidonPermutation (absorb
      (poseidonPermutation (absorb (spongeInit 0x41530003 18) (digest 500))) middle)) tail)) 7 = _
  rw [first_absorb,permutation_0,middle_absorb,permutation_1,tail_absorb,permutation_2]
  rfl

theorem nonzero : (fixturePublic false).change 7 ≠ 0 := by
  rw [value]
  intro zero
  have values := congrArg (fun a : ZMod 2147483647 => a.val) zero
  change 351017421 = 0 at values
  omega

#print axioms first_absorb
#print axioms middle_absorb
#print axioms tail_absorb
#print axioms value
#print axioms nonzero
end R1Z.PV_RunJoin_TransferSentinel
