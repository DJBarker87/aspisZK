import XRx_FinishStep
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option pp.explicit true in
#print core.slice.iter.IteratorIterMut.next
#check Slice.getElem_eq
#check Slice.getElem_val
#check core.slice.iter.IteratorIterMut.next_spec
#check Lean.Meta.withTransparency
