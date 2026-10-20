import CuSavingsGeometryRow
set_option autoImplicit false
namespace AspisR1.CuSavingsGeometryDispatch
open Aeneas Aeneas.Std Result AspisR1GeometryCandidate7
open CuSavingsGeometryNode CuSavingsGeometryRow

theorem unchanged_node (folds index : Usize) : new.node folds index=old.node folds index := by rfl

theorem cached_node (cache : alloc.vec.Vec M) (index start : Usize) (z : M)
    (hs : start.val≤index.val) (hb : index.val-start.val<cache.val.length)
    (hz : cache.val.getD (index.val-start.val) field.M31.ZERO=z) :
    new.cached_node (alloc.vec.Vec.deref cache) index start=step z := by
  obtain ⟨offset,hsub,hval⟩ := WP.spec_imp_exists
    (UScalar.sub_spec (x:=index) (y:=start) (by scalar_tac))
  have hv : offset.val=index.val-start.val := hval
  have hi : offset.val<cache.val.length := by omega
  have hread : Slice.index_usize (alloc.vec.Vec.deref cache) offset=.ok z := by
    unfold Slice.index_usize
    simp only [Slice.getElem?_Usize_eq,alloc.vec.Vec.deref, List.getElem?_eq_getElem hi]
    have hget := List.getD_eq_getElem cache.val field.M31.ZERO hi
    have hz1 : cache.val.getD offset.val field.M31.ZERO=z := by simpa only [hv] using hz
    rw [hz1] at hget
    exact congrArg Result.ok hget.symm
  simp only [new.cached_node,hsub,hread,bind_tc_ok,step]

/-- Exact source selector: only the two-fold branch substitutes cached geometry;
all other variants keep the original accumulation-node computation. -/
def selected (folds : Usize) (cache : alloc.vec.Vec M) (index start u : Usize) : Result M :=
  if folds=2#usize then new.cached_node (alloc.vec.Vec.deref cache) index start else new.node folds u

theorem selected_equivalence (folds : Usize) (cache : alloc.vec.Vec M)
    (index start u : Usize) (query : U32) (z : M)
    (origin : Origin query z) (cast : lift (UScalar.cast .Usize query)=.ok u)
    (hs : start.val≤index.val) (hb : index.val-start.val<cache.val.length)
    (hz : cache.val.getD (index.val-start.val) field.M31.ZERO=z) :
    selected folds cache index start u=old.node folds u := by
  unfold selected
  by_cases hf : folds=2#usize
  · subst folds
    rw [if_pos rfl,cached_node cache index start z hs hb hz,origin_node query z origin u cast]
  · rw [if_neg hf,unchanged_node]

/-- Equality is independent of the unchanged accumulated value/tail and of
all possible results of the shared cryptographic query prefix. -/
theorem query_context {A B : Type} (folds : Usize) (cache : alloc.vec.Vec M)
    (index start u : Usize) (query : U32) (z : M)
    (origin : Origin query z) (cast : lift (UScalar.cast .Usize query)=.ok u)
    (hs : start.val≤index.val) (hb : index.val-start.val<cache.val.length)
    (hz : cache.val.getD (index.val-start.val) field.M31.ZERO=z)
    (before : Result A) (tail : M→A→Result B) :
    (do let value ← before
        let node ← selected folds cache index start u
        tail node value)=
    (do let value ← before
        let node ← old.node folds u
        tail node value) := by
  rw [selected_equivalence folds cache index start u query z origin cast hs hb hz]

#print axioms unchanged_node
#print axioms cached_node
#print axioms selected_equivalence
#print axioms query_context
end AspisR1.CuSavingsGeometryDispatch
