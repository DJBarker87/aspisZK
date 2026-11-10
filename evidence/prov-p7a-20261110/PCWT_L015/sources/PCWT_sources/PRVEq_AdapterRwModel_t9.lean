-- PCWT_ discharge for AdapterRw.r1_pool_adapter.readonly_meta_ok and AdapterRw.r1_pool_adapter.owned.require_readonly_account. Route (b).
-- What was bound (PCWL_ w5): the fresh text (PCWL_E001, frozen 4bb3b3f, ON, original Aeneas) has ONE external, the SDK equality solana_pubkey::Pubkey: PartialEq::eq
-- (crate solana-pubkey, trust row HM-A), the gate slot ops.op36.  Here the Ext carries exactly that field and is built from the slot: x := { pk_eq := ops.op36 }, for EVERY ops.
-- No Aspis external remains; the single residual is the SDK Pubkey equality (HM-A), named in the status record.  core.cmp::PartialEq::ne default and ProgramError resolve to gate declarations.
import Aeneas
import AdapterRwModel
import PRVEq_AdapterRwModel_w5
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 200000
noncomputable section

namespace PRVEq.AdapterRwModel_t9
open AdapterRw

theorem readonly_meta_ok_sdk_pubkey_eq (ops : Ops) :
    PRVFresh_ARM_w5.r1_pool_adapter.readonly_meta_ok { pk_eq := ops.op36 } = AdapterRw.r1_pool_adapter.readonly_meta_ok ops :=
  PRVEq.AdapterRwModel_w5.readonly_meta_ok_eq ops _ rfl

theorem require_readonly_account_sdk_pubkey_eq (ops : Ops) :
    PRVFresh_ARM_w5.r1_pool_adapter.owned.require_readonly_account { pk_eq := ops.op36 } =
    AdapterRw.r1_pool_adapter.owned.require_readonly_account ops :=
  PRVEq.AdapterRwModel_w5.require_readonly_account_eq ops _ rfl

end PRVEq.AdapterRwModel_t9
#print axioms PRVEq.AdapterRwModel_t9.readonly_meta_ok_sdk_pubkey_eq
#print axioms PRVEq.AdapterRwModel_t9.require_readonly_account_sdk_pubkey_eq
