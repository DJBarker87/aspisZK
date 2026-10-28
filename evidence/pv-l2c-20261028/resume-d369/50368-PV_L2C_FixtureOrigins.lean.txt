import PV_L2C_DigestRoundtrip
import PV_L2C_RecordRange
import PV_L2C_CompilerRange
import PV_L2C_FixtureAudit
set_option autoImplicit false
noncomputable section
namespace PV_L2C_FixtureOrigins
open Aeneas Aeneas.Std Result R1Z R0Z.WriterRefine PV_RunJoin_FixtureArguments

theorem key : Canon8 witness.pair.nullifier_key := by
  intro j hj;interval_cases j <;> decide
#print axioms key

theorem salt : Canon8 witness.pair.salt := by
  intro j hj;interval_cases j <;> decide
#print axioms salt

theorem recipient_owner : PV_L2C_DigestOrigin.Origin recipient.owner_key := by
  apply PV_L2C_DigestRoundtrip.origin
  intro j hj;interval_cases j <;> decide
#print axioms recipient_owner

theorem recipient_salt : PV_L2C_DigestOrigin.Origin recipient.salt := by
  apply PV_L2C_DigestRoundtrip.origin
  intro j hj;interval_cases j <;> decide
#print axioms recipient_salt

theorem transfer_change : PV_L2C_DigestOrigin.Origin transferChange.owner_key ∧
    PV_L2C_DigestOrigin.Origin transferChange.salt := by
  constructor <;> apply PV_L2C_DigestRoundtrip.origin
  all_goals intro j hj;interval_cases j <;> decide
#print axioms transfer_change

theorem withdrawal_change : PV_L2C_DigestOrigin.Origin withdrawalChange.owner_key ∧
    PV_L2C_DigestOrigin.Origin withdrawalChange.salt := by
  constructor <;> apply PV_L2C_DigestRoundtrip.origin
  all_goals intro j hj;interval_cases j <;> decide
#print axioms withdrawal_change

theorem transfer_fields : PV_L2C_RecordRange.Fields PV_RunJoin_AdmittedCarrier23.transfer := by
  refine ⟨key,salt,by decide,by decide,?_,transfer_change.1,transfer_change.2⟩
  intro note he
  change some recipient = some note at he
  cases Option.some.inj he
  exact ⟨recipient_owner,recipient_salt⟩
#print axioms transfer_fields

theorem withdrawal_fields : PV_L2C_RecordRange.Fields PV_RunJoin_AdmittedCarrier23.withdrawal := by
  refine ⟨key,salt,by decide,by decide,?_,withdrawal_change.1,withdrawal_change.2⟩
  intro note he
  change none = some note at he
  cases he
#print axioms withdrawal_fields

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]
include K in
theorem both :
    (∀ c r, (PV_Src_Forest_Columns.read PV_RunJoin_AdmittedCarrier23.transfer.compiled.semantic_c1.c1 c r).val < 2147483647) ∧
    (∀ c r, (PV_Src_Forest_Columns.read PV_RunJoin_AdmittedCarrier23.withdrawal.compiled.semantic_c1.c1 c r).val < 2147483647) := by
  constructor
  · exact (PV_L2C_CompilerRange.source
      (⟨_,PV_L2C_FixtureAudit.transfer (K:=K)⟩ : PV_L2C_HonestCaller.Family (K:=K))
      transfer_fields (by change (77#u32 : U32).val < 2147483647;scalar_tac)).2
  · exact (PV_L2C_CompilerRange.source
      (⟨_,PV_L2C_FixtureAudit.withdrawal (K:=K)⟩ : PV_L2C_HonestCaller.Family (K:=K))
      withdrawal_fields (by change (77#u32 : U32).val < 2147483647;scalar_tac)).2
#print axioms both
end PV_L2C_FixtureOrigins
