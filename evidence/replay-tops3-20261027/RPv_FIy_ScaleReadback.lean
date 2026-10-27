import RPv_FIy_WritebackCells
import RPv_FIy_IteratorCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIy_ScaleReadback
open Aeneas Aeneas.Std Result FIq_Native
open FIy_IteratorTraversal
open FIv_NativeValue (Canon decode)
open FIw_ArrayValue (canonical decoded)

def run (range : Array QM 33#usize) (selector : QM) : Result (Array QM 33#usize) := do
  let (iter,into_back) ← MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter range
  let (im,back) ← Loop3 iter (fun x=>x) selector
  ok (into_back (back im))

theorem readback (a : Array QM 33#usize) (im : IterMut) (v : Nat → QM)
    (hlen : im.slice.val.length=33) :
    (a.val.mapIdx (fun i old =>
      (deferredWrites v 0 33 im).slice.val[i]?.getD old)) =
        List.ofFn (fun i : Fin 33 => v i.val) := by
  apply List.ext_getElem?
  intro j
  by_cases hj : j < 33
  · have ha : j < a.val.length := by rw [a.property];exact hj
    rw [List.getElem?_mapIdx,List.getElem?_eq_getElem ha,
      FIy_WritebackCells.value v 0 33 im j (by omega),if_pos (by omega)]
    simp only [Option.getD_some,Option.map_some,List.getElem?_ofFn,hj,↓reduceDIte]
  · rw [List.getElem?_eq_none (by rw [List.length_mapIdx,a.property];change 33≤j;omega),
      List.getElem?_eq_none (by simp only [List.length_ofFn];omega)]

#print axioms readback
end AspisR1.FIy_ScaleReadback
end
