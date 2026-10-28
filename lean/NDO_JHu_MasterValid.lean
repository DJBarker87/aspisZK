import NDO_JHu_MasterPolicy
import NCV_SequenceValidation
set_option autoImplicit false
namespace AspisR1.JHu_MasterValid
open Aeneas Aeneas.Std Result
attribute [local irreducible] JHg_DataMaster.bytes

theorem source : NCV_Reference.valid_master
    (NCV_Carrier.fromMaster JHg_AccountValues.master)=ok true := by
  have pool : NCV_Reference.zero JHg_AccountValues.master.identity.pool.to_slice=ok false := by
    apply JHu_ZeroFields.nonzero
    · change 32 ≤ 768;omega
    · change (34#u8 : U8) ≠ 0#u8;scalar_tac
    · change 0<32;omega
  have mint : NCV_Reference.zero JHg_AccountValues.master.identity.asset_mint.to_slice=ok false := by
    apply JHu_ZeroFields.nonzero
    · change 32 ≤ 768;omega
    · change (66#u8 : U8) ≠ 0#u8;scalar_tac
    · change 0<32;omega
  have token : NCV_Reference.zero JHg_AccountValues.master.identity.token_program.to_slice=ok false := by
    apply JHu_ZeroFields.nonzero
    · change JHg_AccountValues.master.identity.token_program.val.length ≤ 768
      rw [JHg_AccountValues.master.identity.token_program.property];scalar_tac
    · change (((JHg_DataMaster.bytes.drop 136).take 32)[0]?).getD 0#u8 ≠ 0#u8
      rw [JHg_AuditMaster.token]
      change (6#u8 : U8) ≠ 0#u8;scalar_tac
    · change 0<JHg_AccountValues.master.identity.token_program.val.length
      rw [JHg_AccountValues.master.identity.token_program.property];scalar_tac
  have domain : NCV_Reference.zero JHg_AccountValues.master.identity.deployment_domain.to_slice=ok false := by
    apply JHu_ZeroFields.nonzero
    · change JHg_AccountValues.master.identity.deployment_domain.val.length ≤ 768
      rw [JHg_AccountValues.master.identity.deployment_domain.property];scalar_tac
    · change (((JHg_DataMaster.bytes.drop 176).take 32)[0]?).getD 0#u8 ≠ 0#u8
      rw [JHg_AuditMaster.domain]
      change (5#u8 : U8) ≠ 0#u8;scalar_tac
    · change 0<JHg_AccountValues.master.identity.deployment_domain.val.length
      rw [JHg_AccountValues.master.identity.deployment_domain.property];scalar_tac
  have seq : NCV_Reference.valid_sequences (Array.repeat 8#usize 0#u64)=ok true := by
    apply NCV_SequenceValidation.valid
    intro j hj
    rw [NCV_ArrayRead.repeat_value _ _ j (by simpa using hj)]
    scalar_tac
  have zero : NCV_Reference.zero_sequences (Array.repeat 8#usize 0#u64)=ok true := by
    apply NCV_SequenceValidation.zero
    intro j hj
    exact NCV_ArrayRead.repeat_value _ _ j (by simpa using hj)
  have counter : ¬JHg_AccountValues.master.next_checkpoint_sequence=0#u64 := by
    change core.num.U64.from_le_bytes JHg_Scalar00.value ≠0#u64
    rw [JHg_Scalar00.native]
    scalar_tac
  change (do
    let b ← NCV_Reference.zero JHg_AccountValues.master.identity.pool.to_slice
    if b then ok false else do
      let b1 ← NCV_Reference.zero JHg_AccountValues.master.identity.asset_mint.to_slice
      if b1 then ok false else do
        let b2 ← NCV_Reference.zero JHg_AccountValues.master.identity.token_program.to_slice
        if b2 then ok false else do
          let b3 ← NCV_Reference.zero JHg_AccountValues.master.identity.deployment_domain.to_slice
          if b3 then ok false else do
            let b4 ← NCV_Reference.valid_policy (NCV_Carrier.fromPolicy JHg_AccountValues.master.verifier_policy)
            if b4 then do
              let b5 ← NCV_Reference.valid_sequences (Array.repeat 8#usize 0#u64)
              if b5 then do
                let _ ← NCV_Reference.zero_sequences (Array.repeat 8#usize 0#u64)
                if JHg_AccountValues.master.next_checkpoint_sequence=0#u64 then ok false else ok true
              else ok false
            else ok false)=_
  simp only [pool,mint,token,domain,JHu_MasterPolicy.valid,seq,zero,bind_tc_ok,
    Bool.false_eq_true,ite_false,ite_true,counter]
#print axioms source
end AspisR1.JHu_MasterValid
