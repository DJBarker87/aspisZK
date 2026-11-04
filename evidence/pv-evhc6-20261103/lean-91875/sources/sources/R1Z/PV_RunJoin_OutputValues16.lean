import R1Z.PV_RunJoin_OutputRecipient16
import R1Z.PV_RunJoin_OutputTransferChange16
import R1Z.PV_RunJoin_OutputWithdrawalChange16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OutputValues16
open R0P PV_RunJoin_OutputModel16 PV_RunJoin_FixtureRecords
attribute [local irreducible] poseidonPermutation
def recipient_chunk2 : Fin 8 → Scalar := fun i =>
  if i.val = 0 then 600 else if i.val = 1 then 77 else (digest 400) ⟨i.val-2,by omega⟩
def recipient_chunk3 : Fin 8 → Scalar := fun i =>
  if h : i.val < 2 then (digest 400) ⟨i.val+6,by omega⟩ else 0

theorem recipient_init : absorb (spongeInit (0x41530003 : Scalar) 18) (digest 300) = s_30_0 := by
  funext i; fin_cases i <;> rfl

theorem recipient_absorb2 : absorb s_30_23 recipient_chunk2 = s_31_0 := by
  funext i; fin_cases i <;> rfl

theorem recipient_absorb3 : absorb s_31_23 recipient_chunk3 = s_32_0 := by
  funext i; fin_cases i <;> rfl

theorem recipient : noteCommitment (digest 300) (600 : Scalar) 77 (digest 400) = digestOf s_32_23 := by
  change digestOf (spongeStep (spongeStep (spongeStep (spongeInit 0x41530003 18)
    (digest 300)) recipient_chunk2) recipient_chunk3) = _
  unfold spongeStep
  rw [recipient_init,permutation_30,recipient_absorb2,permutation_31,recipient_absorb3,permutation_32]
#print axioms recipient_init
#print axioms recipient_absorb2
#print axioms recipient_absorb3
#print axioms recipient
def transfer_change_chunk2 : Fin 8 → Scalar := fun i =>
  if i.val = 0 then 400 else if i.val = 1 then 77 else (digest 600) ⟨i.val-2,by omega⟩
def transfer_change_chunk3 : Fin 8 → Scalar := fun i =>
  if h : i.val < 2 then (digest 600) ⟨i.val+6,by omega⟩ else 0

theorem transfer_change_init : absorb (spongeInit (0x41530003 : Scalar) 18) (digest 500) = s_33_0 := by
  funext i; fin_cases i <;> rfl

theorem transfer_change_absorb2 : absorb s_33_23 transfer_change_chunk2 = s_34_0 := by
  funext i; fin_cases i <;> rfl

theorem transfer_change_absorb3 : absorb s_34_23 transfer_change_chunk3 = s_35_0 := by
  funext i; fin_cases i <;> rfl

theorem transfer_change : noteCommitment (digest 500) (400 : Scalar) 77 (digest 600) = digestOf s_35_23 := by
  change digestOf (spongeStep (spongeStep (spongeStep (spongeInit 0x41530003 18)
    (digest 500)) transfer_change_chunk2) transfer_change_chunk3) = _
  unfold spongeStep
  rw [transfer_change_init,permutation_33,transfer_change_absorb2,permutation_34,transfer_change_absorb3,permutation_35]
#print axioms transfer_change_init
#print axioms transfer_change_absorb2
#print axioms transfer_change_absorb3
#print axioms transfer_change
def withdrawal_change_chunk2 : Fin 8 → Scalar := fun i =>
  if i.val = 0 then 750 else if i.val = 1 then 77 else (digest 800) ⟨i.val-2,by omega⟩
def withdrawal_change_chunk3 : Fin 8 → Scalar := fun i =>
  if h : i.val < 2 then (digest 800) ⟨i.val+6,by omega⟩ else 0

theorem withdrawal_change_init : absorb (spongeInit (0x41530003 : Scalar) 18) (digest 700) = s_36_0 := by
  funext i; fin_cases i <;> rfl

theorem withdrawal_change_absorb2 : absorb s_36_23 withdrawal_change_chunk2 = s_37_0 := by
  funext i; fin_cases i <;> rfl

theorem withdrawal_change_absorb3 : absorb s_37_23 withdrawal_change_chunk3 = s_38_0 := by
  funext i; fin_cases i <;> rfl

theorem withdrawal_change : noteCommitment (digest 700) (750 : Scalar) 77 (digest 800) = digestOf s_38_23 := by
  change digestOf (spongeStep (spongeStep (spongeStep (spongeInit 0x41530003 18)
    (digest 700)) withdrawal_change_chunk2) withdrawal_change_chunk3) = _
  unfold spongeStep
  rw [withdrawal_change_init,permutation_36,withdrawal_change_absorb2,permutation_37,withdrawal_change_absorb3,permutation_38]
#print axioms withdrawal_change_init
#print axioms withdrawal_change_absorb2
#print axioms withdrawal_change_absorb3
#print axioms withdrawal_change
end R1Z.PV_RunJoin_OutputValues16
