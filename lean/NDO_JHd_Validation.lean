import NDO_JHd_ReferenceSlots
import NDO_JHd_ProofRead
import NDO_JHd_ScanValue
import NDO_JGx_Validated
import AdapterRwScalar
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHd_Validation
open Aeneas Aeneas.Std Result S2W_D189Wrappers
open _root_.AdapterRw
attribute [local irreducible] JHb_World.e2 JHb_Header.account JHb_DataRequest.value
  JHd_RequestCarrier.actual JGx_RealStatement.value
  r1_pool_adapter.owned.authenticate_asq8_accounts
  r1_pool_adapter.owned.OwnedAccount.data

theorem request_size :
    aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES=ok 320#usize := by
  unfold aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES
    aspis_statement.pool_v1.payment_relation.POOL_V1_PAYMENT_STATEMENT_BYTES
  rw [AdapterRw.Scalar.mul_eq 3#usize 32#usize 96#usize (by scalar_tac),bind_tc_ok,
    AdapterRw.Scalar.add_eq 8#usize 96#usize 104#usize (by scalar_tac),bind_tc_ok]
  exact AdapterRw.Scalar.add_eq _ _ _ (by scalar_tac)
#print axioms request_size

theorem source (base : Ops) (slot : U64) (authenticated : r1_pool_adapter.AuthenticatedAsq8Accounts)
    (authentication : r1_pool_adapter.owned.authenticate_asq8_accounts (JHd_ReferenceSlots.install base)
      CPH_Program.verifier (JHb_World.e2.second secondSizes) JHb_Programs.pool 3#u8 slot=
      ok (.Ok authenticated))
    (scan : (JHd_ReferenceSlots.install base).op51 JHb_Header.account=ok (.Ok JHd_ScanValue.value))
    (reconstruction : (JHd_ReferenceSlots.install base).op52 JHd_RequestCarrier.actual authenticated
      JHd_ScanValue.candidate=ok (.Ok JGx_RealStatement.value)) :
    r1_pool_adapter.owned.validate_asq8 (JHd_ReferenceSlots.install base) CPH_Program.verifier
      (JHb_World.e2.second secondSizes) JHb_DataRequest.value (.Ok slot)=ok (.Ok JGx_Validated.value) := by
  have profile : core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
      JHd_RequestCarrier.actual.verifier_profile r1_pool_adapter.PROFILE_BINDING=ok false := by
    rw [JHd_RequestCarrier.profile]
    unfold r1_pool_adapter.PROFILE_BINDING
    rfl
  have release : core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
      JHd_RequestCarrier.actual.verifier_release r1_pool_adapter.RELEASE_BINDING=ok false := by
    rw [JHd_RequestCarrier.release]
    unfold r1_pool_adapter.RELEASE_BINDING
    rfl
  have pool : core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
      JHd_RequestCarrier.actual.pool_program JHb_Programs.pool=ok false := by
    rw [JHd_RequestCarrier.pool]
    rfl
  have pool_id : (JHd_ReferenceSlots.install base).op45=ok JHb_Programs.pool := rfl
  have pool_key : (JHd_ReferenceSlots.install base).op37 JHd_RequestCarrier.actual.pool_program=
      ok JHb_Programs.pool := by rw [JHd_RequestCarrier.pool];rfl
  unfold r1_pool_adapter.owned.validate_asq8
  simp only [JHb_RequestCarrier.length,request_size,bind_tc_ok,
    show (320#usize !=320#usize)=false from rfl,Bool.false_eq_true,↓reduceIte,
    JHd_ReferenceSlots.decode,core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,
    profile,release,pool_id,pool,pool_key,JHd_ReferenceSlots.nullifier,JHd_ReferenceSlots.lane,
    authentication,JHd_ProofRead.first,core.option.Option.ok_or,JHd_ProofRead.data,
    scan,reconstruction,JHd_ScanValue.value,JGx_Validated.value]
#print axioms source
end AspisR1.JHd_Validation
end
