import NFB_RootGather
import NEW_GeometryReverse
set_option autoImplicit false
namespace NFB_ReverseTrace
open Aeneas.Std AspisR1 NFB_PhysicalFrame NFB_PrivateFrame
open S7Kani2PrefixLoop (wordMul)
open Port4C_BatchInverse (cell)

def writes (flat prefixes : List U32) : Nat → U32 → List Action
 | 0,_ => []
 | n+1,s => store .inverse n (wordMul s (cell prefixes n)) ::
    writes flat prefixes n (wordMul s (cell flat n))

theorem complete (flat prefixes inverse : List U32) (n : Nat) (suffix : U32)
 (bound : n ≤ inverse.length) :
 NEW_GeometryReverse.Trace flat prefixes n inverse suffix
  (Port4C_OwnedInverse.model flat prefixes n inverse suffix)
  (NEW_GeometryReverse.suffixAfter flat n suffix)
  (NEW_GeometryReverse.callLog flat prefixes n suffix) := by
 induction n generalizing inverse suffix with
 | zero => exact NEW_GeometryReverse.Trace.done _ _
 | succ n ih =>
  apply NEW_GeometryReverse.Trace.step n inverse
   (inverse.set n (wordMul suffix (cell prefixes n)))
   (Port4C_OwnedInverse.model flat prefixes (n+1) inverse suffix)
   suffix (NEW_GeometryReverse.suffixAfter flat (n+1) suffix)
   (NEW_GeometryReverse.callLog flat prefixes n (wordMul suffix (cell flat n)))
  · omega
  · exact List.length_set
  · intro j hj
    by_cases same : j=n
    · subst j
      simp only [ite_true,List.getElem?_set_self (by omega : n < inverse.length)]
    · simp only [same,if_false,List.getElem?_set_ne (Ne.symm same)]
  · exact ih _ _ (by simpa only [List.length_set] using (show n ≤ inverse.length by omega))

theorem owned (flat prefixes : List U32) (n : Nat) (suffix : U32) :
 ∀ a∈writes flat prefixes n suffix,Private a := by
 induction n generalizing suffix with
 | zero => simp [writes]
 | succ n ih =>
  intro a ha
  simp only [writes,List.mem_cons] at ha
  rcases ha with rfl | ha
  · exact Private.store _ _ _
  · exact ih _ a ha

theorem payload (flat prefixes inverse : List U32) (n : Nat) (suffix : U32)
 (heap : Heap) (selected : heap Place.inverse.id=some inverse) :
 NFB_PhysicalFrame.run (writes flat prefixes n suffix) heap Place.inverse.id=
 some (Port4C_OwnedInverse.model flat prefixes n inverse suffix) := by
 induction n generalizing inverse suffix heap with
 | zero => exact selected
 | succ n ih =>
  change NFB_PhysicalFrame.run
   (writes flat prefixes n (wordMul suffix (cell flat n)))
   ((store .inverse n (wordMul suffix (cell prefixes n))).apply heap)
   Place.inverse.id=_
  apply ih
  simp only [store,Action.apply,write,ite_true,selected,Option.map_some,cell]
#print axioms complete
#print axioms owned
#print axioms payload
end NFB_ReverseTrace
