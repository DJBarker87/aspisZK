import NNK_COMBINED_IMPORT
open AspisR1
example : RSL.TX1_087.RowSpec_087 LIB_Instances.VL LIB_Instances.P NNG_Producer087.producer := NNG_Candidate087.candidate
example (a : RSL.TX1_087.Args LIB_Instances.VL) (obs : RSL.Observer) :
 RSL.TX1_087.Domain LIB_Instances.VL a obs =
 (a.proof.length = RSL.VPROOF_BYTES ∧ obs = none ∧ LIB_Instances.VL.publicDom a.public_ ∧
 LIB_Instances.VL.checkValuesDom (RSL.slice a.proof RSL.OFF_Y1 RSL.OFF_INACTIVE)) := rfl
#print NNG_Candidate087.candidate
#print NNG_Producer087.producer
#print NNG_PreparedOccurrence087.occurrence
#print NNG_ReadyFront087.returned
#print RSL.TX1_087.RowSpec_087
#print LIB_Instances.VL
#print LIB_Instances.P
#print axioms NNG_Candidate087.candidate
#print axioms NNG_Producer087.source
#print axioms NNG_PreparedOccurrence087.occurrence
#print axioms RSL.TX1_087.domain_needs_R4
#print axioms RSL.TX1_087.rejects_wrong_g
