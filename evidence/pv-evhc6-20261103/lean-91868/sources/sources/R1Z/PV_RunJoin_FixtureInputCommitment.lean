import R1Z.PV_RunJoin_FixtureOwnerKey
import R1Z.PV_RunJoin_FixtureHashCell1
import R1Z.PV_RunJoin_FixtureHashCell2
import R1Z.PV_RunJoin_FixtureHashCell3

/-! Exact mathematical input commitment on the fixture arguments. This closes
a literal-value fact, not the native Records or compiler association. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_FixtureHashModel
open R0P PV_RunJoin_FixtureRecords

def noteChunk2 : Fin 8 → Scalar := fun i =>
  if i.val = 0 then 1000 else if i.val = 1 then 77 else (digest 100) ⟨i.val-2,by omega⟩
def noteChunk3 : Fin 8 → Scalar := fun i =>
  if h : i.val < 2 then (digest 100) ⟨i.val+6,by omega⟩ else 0

theorem note_init : absorb (spongeInit (0x41530003 : Scalar) 18) (digestOf s_0_23) = s_1_0 := by
  funext i
  fin_cases i <;> rfl

theorem note_absorb2 : absorb s_1_23 noteChunk2 = s_2_0 := by
  funext i
  fin_cases i <;> rfl

theorem note_absorb3 : absorb s_2_23 noteChunk3 = s_3_0 := by
  funext i
  fin_cases i <;> rfl

theorem input_commitment : noteCommitment (ownerKey (digest 10)) (1000 : Scalar) 77 (digest 100) =
    digestOf s_3_23 := by
  rw [owner_key]
  change digestOf (spongeStep (spongeStep (spongeStep (spongeInit 0x41530003 18)
    (digestOf s_0_23)) noteChunk2) noteChunk3) = _
  unfold spongeStep
  rw [note_init,permutation_1,note_absorb2,permutation_2,note_absorb3,permutation_3]

#print axioms note_init
#print axioms note_absorb2
#print axioms note_absorb3
#print axioms input_commitment
end R1Z.PV_RunJoin_FixtureHashModel
