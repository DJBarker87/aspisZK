import XRs_AddStep
open Aeneas Aeneas.Std Result ControlFlow
set_option autoImplicit false
namespace XRs_AddIndexed
open XRs_AddStep
#print Slice.setAtNat
#check List.set_comm
#check List.getElem?_set_ne
#check Array.index_usize_spec
#check Array.update_spec
#check Array.update_eq
#check Array.index_usize_eq
#check UScalar.add_spec
#check Slice.ext
#check Array.eq_of_val_eq
#check List.getElem?_eq_getElem
#print AspisR1Post25SamplerIndexedAddSmallCandidate.field.P
end XRs_AddIndexed
