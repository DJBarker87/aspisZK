import R1Z.PV_Op223_Agreement_QM31_mul_m31
import R1Z.PV_Op223_Extract_25_compress
import R1Z.PV_Ext_ClosedCandidate
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Op223_ExtractBridge
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull

theorem body : PV_Op223_Applied.prover_shared.compress_tagged_tuple_loop.body =
    PV_Ext_IndexClosed.compress_tagged_tuple_loop.body := by
  funext values lambda out power i
  unfold PV_Op223_Applied.prover_shared.compress_tagged_tuple_loop.body
    PV_Ext_IndexClosed.compress_tagged_tuple_loop.body
  simp only [PV_Op223_Agreement.QM31_mul_m31, PV_Op223_Agreement.QM31_add,
    PV_Op223_Agreement.QM31_mul]

theorem loop : PV_Op223_Applied.prover_shared.compress_tagged_tuple_loop =
    PV_Ext_IndexClosed.compress_tagged_tuple_loop := by
  funext values lambda out power i
  unfold PV_Op223_Applied.prover_shared.compress_tagged_tuple_loop
    PV_Ext_IndexClosed.compress_tagged_tuple_loop
  rw [body]

theorem extraction : PV_Op223_Applied.prover_shared.compress_tagged_tuple =
    PV_Ext_IndexClosed.compress_tagged_tuple := by
  funext tag values lambda
  unfold PV_Op223_Applied.prover_shared.compress_tagged_tuple
    PV_Ext_IndexClosed.compress_tagged_tuple
  rw [PV_Op223_Agreement.CM31_from_m31, PV_Op223_Agreement.QM31_from_cm31, loop]
#print axioms body
#print axioms loop
#print axioms extraction
end R1Z.PV_Op223_ExtractBridge
