import NNG_Tree328
import NNG_InvokeGraph094
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Child328
open Aeneas Aeneas.Std Result NMT_CallTree NNG_Observed136 NNG_Carriers328

theorem observation (a : NNG_Native328.Args) (env : RSL.Env) :
 NNG_Observed136.observation childPort (NNG_Tree328.events env) (NNG_Tree328.child a env)=
 NNG_ProducerFull094.producer (NNG_Native328.args a) none env := by
 unfold NNG_Tree328.child
 rw [NNG_InvokeGraph094.observation,NNG_Tree328.child_call]
 change LIB_Carriers.resultObs childPort
  (NNG_ProducerFull094.producer (NNG_Native328.args a) none env).events
  (NMP_ResultTransport.outer childReply (NNG_Context094.body (NNG_InstalledCalls094.calls env)
   (NNG_Input094.input (NNG_Native328.args a) none env)))=_
 calc
  _=LIB_Carriers.resultObs NNG_ProducerFull094.port
   (NNG_ProducerFull094.producer (NNG_Native328.args a) none env).events
   (NNG_Context094.body (NNG_InstalledCalls094.calls env) (NNG_Input094.input (NNG_Native328.args a) none env)) :=
    NNG_StateCalls094.obs_outer childReply childPort NNG_ProducerFull094.port child_reply _ _
  _=_ := rfl
#print axioms observation

theorem original (a : NNG_Input094.Args) (env : RSL.Env)
 (own : RSL.TX1_094.Domain LIB_Instances.VL a none a.public_) :
 NNG_Observed136.observation childPort (NNG_Tree328.events env) (NNG_Tree328.child (NNG_Native328.input a) env)=
 NNG_ProducerFull094.producer a none env :=
 (observation (NNG_Native328.input a) env).trans
  ((congrArg (fun input=>NNG_ProducerFull094.producer input none env) (NNG_Native328.args_input a)).trans
   (NNG_Lower094.observation a env own))
#print axioms original
end AspisR1.NNG_Child328
