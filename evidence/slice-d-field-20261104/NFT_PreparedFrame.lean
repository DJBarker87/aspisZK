import NFT_PreparedSum3
import RPv_AspisR1PoseidonPreparedChannelNestedSet
set_option autoImplicit false
namespace NFT_PreparedFrame
open Aeneas.Std
open AspisR1PoseidonPreparedChannelArraySet
abbrev Sums := Array (Array U64 3#usize) 3#usize

/-- Same arbitrary-prestate native channel cut: selected cell and every other
cell use the nested-set frame of the actual emitted index_mut back closure. -/
theorem frame (sums : Sums) (component channel c j : Usize) (updated : U64)
    (hc : component.val<3) (hj : channel.val<3)
    (hqueryc : c.val<3) (hqueryj : j.val<3) :
    at3 (at3 (sums.set component ((at3 sums component hc).set channel updated)) c hqueryc) j hqueryj=
      if c.val=component.val then
        if j.val=channel.val then updated else at3 (at3 sums component hc) j hqueryj
      else at3 (at3 sums c hqueryc) j hqueryj :=
  AspisR1PoseidonPreparedChannelNestedSet.cell_nested_set sums component channel c j
    (at3 sums component hc) updated hc hj hqueryc hqueryj rfl

/-- Product/control chronology of the deployed three-product helper. -/
theorem control :
    (List.range 3).flatMap (fun i => (List.range 3).flatMap (fun c => (List.range 3).map (fun j => (i,c,j))))=
      (List.range 27).map (fun n => (n/9,n/3%3,n%3)) := by rfl
#print axioms frame
#print axioms control
end NFT_PreparedFrame
