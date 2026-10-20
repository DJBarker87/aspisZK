import GeometryFlatFoldSource
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CurrentWide.Proof
open AspisR1GeometryInputs.Proof Aeneas.Std.alloc.vec
open AspisR1GeometryGrouping.Proof

theorem geometry_flat_circle_fold_success (queries : Array U32 22#usize)
    (start end1 i : Usize) (inverse zs : Vec U32)
    (hrun : geometryAndInvert concreteQueryValues queries start end1 = .ok (.Ok (inverse,zs)))
    (hi : i.val < end1.val-start.val)
    (alpha a b c d out : FoldE)
    (Ca : CanonicalFold a) (Cb : CanonicalFold b) (Cc : CanonicalFold c)
    (Cd : CanonicalFold d) (Calpha : CanonicalFold alpha)
    (hfold : AspisR1FoldInverses.verifier.circle_fold_with_inverses currentFoldOps alpha
      (Array.make 4#usize [a,b,c,d]) (flatInverseArray inverse i) = .ok out) :
    ∃ (u : AspisR1QueryGeometryActual.domain.FibreIndex) (hu : u.val<262144),
      u.val=(queries.val.getD (start.val+i.val) 0#u32).val ∧ CanonicalFold out ∧
      decodeFold out = AspisV5ComponentCConcreteFoldLinearity.circleFoldValue (decodeFold alpha)
        (algebraMap (ZMod AspisR1FoldInverses.Refinement.P) AspisWideTower.WideExact
          (R1ZCircleFoldMathV1.rustHalf *
            (R17TableCirclePowerBridge.circleCoords
              (AspisV7ExactOneFoldDomains.storedInitialFibrePoint20 ⟨u.val,hu⟩)).re⁻¹))
        (algebraMap (ZMod AspisR1FoldInverses.Refinement.P) AspisWideTower.WideExact
          (R1ZCircleFoldMathV1.rustHalf *
            (R17TableCirclePowerBridge.circleCoords
              (AspisV7ExactOneFoldDomains.storedInitialFibrePoint20 ⟨u.val,hu⟩)).im⁻¹))
        (AspisR1FoldInverses.Refinement.values4 (decodeFold a) (decodeFold b) (decodeFold c) (decodeFold d)) := by
  exact geometry_circle_fold_success queries start end1 i inverse zs hrun hi
    (groupedWord inverse i 0#usize) (groupedWord inverse i 1#usize)
    (groupedWord inverse i 2#usize) (groupedWord inverse i 3#usize) (groupedWord inverse i 4#usize)
    (inverse,i) (inverse,i)
    (geometry_callback_total queries start end1 i 0#usize inverse zs hrun hi (by change (0:Nat) < 5; decide))
    (geometry_callback_total queries start end1 i 1#usize inverse zs hrun hi (by change (1:Nat) < 5; decide))
    alpha a b c d out Ca Cb Cc Cd Calpha hfold
#print axioms geometry_flat_circle_fold_success
end AspisR1CurrentWide.Proof
