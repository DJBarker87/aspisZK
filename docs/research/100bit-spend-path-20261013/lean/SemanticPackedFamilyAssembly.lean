import SemanticPackedIntervalAssembly
import R0P.SemDecision

/-! Connect the six source packing contributions to the existing arbitrary-
point scalarLaneAt used by the retained terminal soundness theorem. -/
set_option autoImplicit false
namespace AspisR1.SemanticPackedFamilyAssembly
open AspisR1.ValueLaneResidualList
open AspisR1.SemanticPackedIntervalAssembly
variable {K : Type} [Field K]

theorem family_lengths (pub : R0P.Public K) (o : R0P.Openings K) (sel : R0P.Sel K) :
    ((R0P.scheduleFamily (K := K)).residuals pub o sel).length = 32 ∧
    ((R0P.pathFamily (K := K)).residuals pub o sel).length = 17 ∧
    ((R0P.valueFamily (K := K)).residuals pub o sel).length = 35 ∧
    ((R0P.occupancyFamily (K := K)).residuals pub o sel).length = 12 ∧
    ((R0P.digestFamily (K := K)).residuals pub o sel).length = 8 ∧
    ((R0P.assetFamily (K := K)).residuals pub o sel).length = 2 := by
  simp only [R0P.scheduleFamily, R0P.pathFamily, R0P.pathLanes, R0P.valueFamily,
    R0P.valueRange, R0P.occupancyFamily, R0P.occupancyLanesLiteral, R0P.digestFamily,
    R0P.assetFamily, R0P.assetScalarLanes, List.length_append, List.length_ofFn,
    List.length_cons, List.length_nil, List.length_map]
  all_goals decide

theorem slot_eq_scalarLaneAt (pub : R0P.Public K) (o : R0P.Openings K) (sel : R0P.Sel K)
    (index : Nat) :
    slot ((R0P.scheduleFamily (K := K)).residuals pub o sel)
      ((R0P.pathFamily (K := K)).residuals pub o sel)
      ((R0P.valueFamily (K := K)).residuals pub o sel)
      ((R0P.occupancyFamily (K := K)).residuals pub o sel)
      ((R0P.digestFamily (K := K)).residuals pub o sel)
      ((R0P.assetFamily (K := K)).residuals pub o sel) index =
      R0P.SemSource.scalarLaneAt pub o sel index := rfl

theorem packed_family_contributions {F : Subfield K} (B : R0P.PackBasis F)
    (pub : R0P.Public K) (o : R0P.Openings K) (sel : R0P.Sel K) (group : Nat) :
    (((((R0P.pack4 B (fun k => selectList 0 ((R0P.scheduleFamily (K := K)).residuals pub o sel) (4*group+k.val)) +
      R0P.pack4 B (fun k => selectList 32 ((R0P.pathFamily (K := K)).residuals pub o sel) (4*group+k.val))) +
      R0P.pack4 B (fun k => selectList 49 ((R0P.valueFamily (K := K)).residuals pub o sel) (4*group+k.val))) +
      R0P.pack4 B (fun k => selectList 0 ((R0P.occupancyFamily (K := K)).residuals pub o sel) (4*group+k.val))) +
      R0P.pack4 B (fun k => selectList 84 ((R0P.digestFamily (K := K)).residuals pub o sel) (4*group+k.val))) +
      R0P.pack4 B (fun k => selectList 92 ((R0P.assetFamily (K := K)).residuals pub o sel) (4*group+k.val))) =
      R0P.pack4 B (fun k => R0P.SemSource.scalarLaneAt pub o sel (4*group+k.val)) := by
  obtain ⟨hs,hp,hv,ho,hd,ha⟩ := family_lengths pub o sel
  exact pack_intervals B _ _ _ _ _ _ hs hp hv ho hd ha group

#print axioms family_lengths
#print axioms slot_eq_scalarLaneAt
#print axioms packed_family_contributions
end AspisR1.SemanticPackedFamilyAssembly
