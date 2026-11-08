import NMX_R4_NMSCarrier
import NMS_R2N_RSLScalarEq
set_option autoImplicit false
namespace NMX_R5_Size242
open Aeneas Aeneas.Std Result AdapterRw

theorem request :
 aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES = .ok 320#usize := by
 have spec : aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES
   ⦃ r => r.val = 320 ⦄ := by
  unfold aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES
  unfold aspis_statement.pool_v1.payment_relation.POOL_V1_PAYMENT_STATEMENT_BYTES
  step*
 obtain ⟨r,run,value⟩ := Aeneas.Std.WP.spec_imp_exists spec
 have same : r = 320#usize := by scalar_tac
 simpa only [same] using run

theorem value : (320#usize).val = RSL.REQUEST_BYTES := by
 unfold RSL.REQUEST_BYTES
 scalar_tac

theorem guard (data : Slice U8) :
 (Slice.len data != 320#usize) = ((NMS_R2N_RSLScalars.bytes data).length != RSL.REQUEST_BYTES) := by
 rw [NMS_R2N_RSLScalarEq.scalar_bne,NMX_R2_LengthGuard.value,value,
  NMS_R2N_RSLScalars.bytes_length]
 by_cases same : data.val.length = RSL.REQUEST_BYTES <;> simp [same]
#print axioms request
#print axioms value
#print axioms guard
end NMX_R5_Size242
