import NNG_Candidate094
import NNG_Candidate328
import LIB_FullInstances
set_option autoImplicit false
noncomputable section
namespace NNL_Domains
open AspisR1

theorem exact094 : RSL.TX1_094.RowSpec_094 LIB_FullInstances.VL LIB_FullInstances.P
 NNG_ProducerFull094.producer := NNG_Candidate094.candidate

theorem exact328 : RSL.TX1_328.RowSpec_328 LIB_FullInstances.VL LIB_FullInstances.P
 NNG_Producer328.producer := NNG_Candidate328.candidate

theorem domain094 (a : RSL.TX1_094.Args LIB_Instances.VL) (obs : RSL.Observer) :
 RSL.TX1_094.Domain LIB_Instances.VL a obs a.public_ =
 (obs = none ∧ LIB_Instances.VL.publicDom a.public_ ∧ a.public_bytes.length = 1880) := rfl

theorem domain328 (a : RSL.TX1_094.Args LIB_Instances.VL) :
 RSL.TX1_328.Domain LIB_Instances.VL a =
 (LIB_Instances.VL.publicDom a.public_ ∧ a.public_bytes.length = 1880) := rfl


#print axioms exact094
#print axioms exact328
#print axioms domain094
#print axioms domain328
end NNL_Domains
