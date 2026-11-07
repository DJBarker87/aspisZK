import PCM_Carriers
set_option autoImplicit false
namespace PCM_POOL_220
open RSL PCM
inductive Error where
  | nonCanonicalCommitment | nonCanonicalOccupancy | nonCanonicalInverse
  | occupancyNotBoolean | sentinelInverseMismatch | emptyInverseNonZero
  | emptyCommitmentNonZero | occupiedSentinelZero | selectedSlotEmpty
  deriving DecidableEq

def modulus : Nat := 2147483647
def mul (a b : UInt32) : Nat := a.toNat * b.toNat % modulus

def validate (w : PairWitness) : Except Error Unit := do
  if !(w.first_commitment.all (fun n => decide (n < P31))) ||
      !(w.second_commitment.all (fun n => decide (n < P31))) then throw .nonCanonicalCommitment
  if w.second_occupied ≥ P31 then throw .nonCanonicalOccupancy
  if w.second_occupancy_inverse ≥ P31 then throw .nonCanonicalInverse
  let oneMinus := (1 + modulus - w.second_occupied.toNat) % modulus
  let occupiedMinusOne := (w.second_occupied.toNat + modulus - 1) % modulus
  if w.second_occupied.toNat * occupiedMinusOne % modulus != 0 then throw .occupancyNotBoolean
  let sentinel := w.second_commitment.getD 7 0
  if mul sentinel w.second_occupancy_inverse != w.second_occupied.toNat then throw .sentinelInverseMismatch
  if oneMinus * w.second_occupancy_inverse.toNat % modulus != 0 then throw .emptyInverseNonZero
  if w.second_commitment.any (fun limb => oneMinus * limb.toNat % modulus != 0) then throw .emptyCommitmentNonZero
  if w.second_occupied == 1 && sentinel == 0 then throw .occupiedSentinelZero
  pure ()

def model (parent : Digest → Digest → Digest) (w : PairWitness) : Except Error Digest := do
  validate w
  pure (parent w.first_commitment w.second_commitment)
def Domain (w : PairWitness) : Prop := w.first_commitment.length = 8 ∧ w.second_commitment.length = 8

def RowSpec (parent : Digest → Digest → Digest)
    (impl : PairWitness → Env → Obs (Except Error Digest)) : Prop :=
  ∀ w, Domain w → ∀ env, impl w env = ⟨.ret (model parent w),[]⟩

/-- Reject the wrong enum constructor without reducing any field products. -/
theorem rejects_wrong_error (parent : Digest → Digest → Digest) :
    ¬ RowSpec parent (fun _ _ => ⟨.ret (.error .nonCanonicalInverse),[]⟩) := by
  intro h
  let w : PairWitness := ⟨List.replicate 8 P31,List.replicate 8 0,0,0⟩
  have hw : Domain w := ⟨rfl,rfl⟩
  have hr := h w hw env0
  have hm : model parent w = .error .nonCanonicalCommitment := rfl
  rw [hm] at hr
  cases hr
#print axioms rejects_wrong_error
end PCM_POOL_220
