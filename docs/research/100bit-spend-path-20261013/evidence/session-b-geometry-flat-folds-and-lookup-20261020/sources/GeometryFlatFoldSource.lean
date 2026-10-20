import GeometryGroupingTotal
import GeometryStoredParentFold
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CurrentWide.Proof
open AspisR1GeometryInputs.Proof Aeneas.Std.alloc.vec
open AspisR1GeometryGrouping.Proof
private abbrev Callback := AspisR1GeometryGrouping.geometry_groups.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut

def flatInverseArray (inverse : Vec U32) (i : Usize) : Array U32 5#usize :=
  Array.make 5#usize [groupedWord inverse i 0#usize,groupedWord inverse i 1#usize,
    groupedWord inverse i 2#usize,groupedWord inverse i 3#usize,groupedWord inverse i 4#usize]

theorem geometry_callback_total (queries : Array U32 22#usize)
    (start end1 i j : Usize) (inverse zs : Vec U32)
    (hrun : geometryAndInvert concreteQueryValues queries start end1 = .ok (.Ok (inverse,zs)))
    (hi : i.val < end1.val-start.val) (hj : j.val < 5) :
    Callback (inverse,i) j = .ok (groupedWord inverse i j,(inverse,i)) := by
  obtain ⟨_,_,_,_,_,_,_,_,hlen,_⟩ := concrete_geometry_inverse_success queries start end1 inverse zs hrun
  exact grouping_callback_total inverse i j (by omega)

theorem geometry_flat_line_fold_parent_success (queries : Array U32 22#usize)
    (start end1 i : Usize) (inverse zs : Vec U32)
    (hrun : geometryAndInvert concreteQueryValues queries start end1 = .ok (.Ok (inverse,zs)))
    (hi : i.val < end1.val-start.val)
    (alpha a b c d out : FoldE)
    (Ca : CanonicalFold a) (Cb : CanonicalFold b) (Cc : CanonicalFold c)
    (Cd : CanonicalFold d) (Calpha : CanonicalFold alpha)
    (hfold : AspisR1FoldInverses.verifier.line_fold_with_inverses currentFoldOps alpha
      (Array.make 4#usize [a,b,c,d]) (flatInverseArray inverse i) = .ok out) :
    ∃ g : StoredGeometryPoint (queries.val.getD (start.val+i.val) 0#u32),
      CanonicalFold out ∧ storedLineX g ≠ 0 ∧ storedLineY g ≠ 0 ∧ storedLineZ g ≠ 0 ∧
      decodeFold out = AspisV5ComponentCConcreteFoldLinearity.lineFoldValue (decodeFold alpha)
        (algebraMap (ZMod AspisR1FoldInverses.Refinement.P) AspisWideTower.WideExact
          (R1ZQueryGeometryValuesV1.sourceLineInverse (storedParent g) 0))
        (algebraMap (ZMod AspisR1FoldInverses.Refinement.P) AspisWideTower.WideExact
          (R1ZQueryGeometryValuesV1.sourceLineInverse (storedParent g) 1))
        (algebraMap (ZMod AspisR1FoldInverses.Refinement.P) AspisWideTower.WideExact
          (R1ZQueryGeometryValuesV1.sourceLineInverse (storedParent g) 2))
        (AspisR1FoldInverses.Refinement.values4 (decodeFold a) (decodeFold b) (decodeFold c) (decodeFold d)) := by
  exact geometry_line_fold_parent_success queries start end1 i inverse zs hrun hi
    (groupedWord inverse i 0#usize) (groupedWord inverse i 1#usize)
    (groupedWord inverse i 2#usize) (groupedWord inverse i 3#usize) (groupedWord inverse i 4#usize)
    (inverse,i) (inverse,i) (inverse,i)
    (geometry_callback_total queries start end1 i 2#usize inverse zs hrun hi (by change (2:Nat) < 5; decide))
    (geometry_callback_total queries start end1 i 3#usize inverse zs hrun hi (by change (3:Nat) < 5; decide))
    (geometry_callback_total queries start end1 i 4#usize inverse zs hrun hi (by change (4:Nat) < 5; decide))
    alpha a b c d out Ca Cb Cc Cd Calpha hfold

#print axioms geometry_callback_total
#print axioms geometry_flat_line_fold_parent_success
end AspisR1CurrentWide.Proof
