import NNI_COMBINED_IMPORT
set_option pp.proofs false
open AspisR1
example : RSL.TX1_136.RowSpec_136 LIB_VLib.library NNG_Producer136.producer :=
  NNG_Candidate136.candidate
example : (NNG_DEnvObserved136.Target LIB_VLib.library NNG_Representation136.project
  NNG_Representation136.calls NNG_Representation136.input NNG_Producer136.events) =
  RSL.TX1_136.RowSpec_136 LIB_VLib.library NNG_Producer136.producer := rfl
example (allocationSucceeded : RSL.Bytes → RSL.Env → Bool) :
  RSL.TX2_217.RowSpec_217 (NMX_R3_DecoderFold.decode allocationSucceeded) :=
  NMX_R3_DecoderFold.root allocationSucceeded
#print NNG_Candidate136.candidate
#print NNG_Producer136.producer
#print LIB_VSemantic.finishInputDom
#print RSL.TX1_136.RowSpec_136
#print RSL.TX2_217.RowSpec_217
#print NMX_R3_DecoderFold.root
#print NMX_R3_LaneAllocation.complete
#print axioms NNG_Candidate136.candidate
#print axioms NMX_R3_DecoderFold.root
#print axioms AspisR1.RPx_Deployed.deployed
