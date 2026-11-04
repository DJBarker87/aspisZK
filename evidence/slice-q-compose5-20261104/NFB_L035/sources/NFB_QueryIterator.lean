import NFB_ZeroFinite
import NDI_IteratorFrame
set_option autoImplicit false
namespace NFB_QueryIterator
open Aeneas Aeneas.Std Result

/-- Native ptr/end denotes this exact suffix of the original protected input,
not another allocation with equal contents. The kernel part is a value view. -/
def view (queries : List U32) (start count cursor : Nat) : List U32 :=
 ((queries.drop start).take count).drop cursor

theorem view_length (queries : List U32) (start count cursor : Nat)
    (fits : start+count≤queries.length) :
    (view queries start count cursor).length=count-cursor := by
 simp only [view,List.length_drop,NDI_IteratorFrame.remainder queries start count fits]

theorem selected (queries : List U32) (start count cursor : Nat)
    (active : cursor<count) :
    ((queries.drop start).take count)[cursor]?=queries[start+cursor]? :=
 NDI_IteratorFrame.selected queries start count cursor active

theorem advance (queries : List U32) (start count cursor : Nat) :
    (view queries start count cursor).drop 1=view queries start count (cursor+1) := by
 simp only [view,List.drop_drop]

/-- The outer iterator uses the SAME coherent next primitive as the zero
scanner, with no arithmetic or child-domain premise. -/
theorem next (it : core.slice.iter.Iter U32) (active : it.i < it.slice.val.length) :
 core.slice.iter.IteratorSliceIter.next it=
  ok (some it.slice.val[it.i],{it with i:=it.i+1}) := NFB_ZeroFinite.next_active it active

theorem end_next (it : core.slice.iter.Iter U32) (finished : it.slice.val.length ≤ it.i) :
 core.slice.iter.IteratorSliceIter.next it=ok (none,it) := NFB_ZeroFinite.next_end it finished

#print axioms view_length
#print axioms selected
#print axioms advance
#print axioms next
#print axioms end_next
end NFB_QueryIterator
