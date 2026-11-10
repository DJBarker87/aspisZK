import NNH8_Exec
import NNH_Run6Installed
/-! NPO_ executable-check triage (step 4 gate). No `noncomputable section`: each probe below is
accepted by the compiler only if every definition it calls has compiled code. A rejection names
the first definition without code. This is a computability probe of the Lean model, not a proof
and not an execution of the recorded bytes. Errors are the expected output where code is absent. -/
set_option autoImplicit false
open Aeneas Aeneas.Std
def NPO_probe_stage1_owned := @AdapterRw.r1_pool_adapter.owned.stage1_owned
def NPO_probe_sdk := @AspisR1.NOC_Run5bCtx.sdk
def NPO_probe_tx1Value := @NNH_ReturnsBundle.tx1Value
def NPO_probe_tx2Value := @NNH_ReturnsBundle.tx2Value
def NPO_probe_producer := @AspisR1.NNG_TotalProducer345.producer
def NPO_probe_implementation := @AspisR1.NNH_Run6Installed.implementation
def NPO_probe_ids_ref := NHJ_IdReference.ids_ref false
#eval (NHJ_IdReference.ids_ref false).isOk
