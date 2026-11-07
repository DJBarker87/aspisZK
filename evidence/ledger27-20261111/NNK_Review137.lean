import NNK_COMBINED_IMPORT
open AspisR1
example : RSL.TX1_137.RowSpec_137 LIB_VLib.library NNG_Producer137.producer := NNG_Candidate137.candidate
example (a : RSL.TX1_137.Args LIB_VLib.library) :
 RSL.TX1_137.Domain LIB_VLib.library a =
 (LIB_VLib.library.publicDom a.public_ ∧ LIB_VLib.library.semanticBytesDom a.bytes) := rfl
#print NNG_Candidate137.candidate
#print NNG_Producer137.producer
#print NNG_FinishOccurrence137.occurrence
#print NNG_Caller136From137.finish_domain
#print RSL.TX1_137.RowSpec_137
#print axioms NNG_Candidate137.candidate
#print axioms NNG_FinishOccurrence137.occurrence
#print axioms NNG_Candidate136.candidate
#print axioms RSL.TX1_137.rejects_constErr
