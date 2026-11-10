import NPH_R22Callbacks
import NPH_R22Installers
import NPH_R22QRawShift
import SAQ_Geometry
import R17FibrePointLineNodeActual
import NEA_TableCanonical
import NFN_GeometryPart05
import NNU_QueryFieldBase
import CurrentWideBaseBridge
import RPu_JFv_RawExtractedSemanticCallOpsV20

/-! NPH_ (R22, separate limb invariant, step 2, second part): geometry callbacks op14/op15
(SAQ_Geometry.line through line_node, SAQ_Geometry.point through fibre_point), the
NFN_NEW_GeometryContextGeneric.replace installer, and the conversion glue (NNU_QueryFieldBase
and CurrentWideBaseBridge toCM/toQM, RawExtractedSemanticCallOpsV20 resultMap and the
genC/genQ/probeC copies).
- fibre_point with the installed R17 CM31 operations: for every fibre index, either the
  checked body returns ok with both coordinates ≤ P (both table reads in bounds; the entries
  are < P by NEA_TableCanonical.readA/readB; R17 new/mul preserve W), or the TABLE_B index
  `index >>> 9` is ≥ 512, an out-of-bounds read that is bounds-checked in both profiles.
- The conversion glue is limb-wise copying, so W transfers unchanged.
Standard axioms; no ops interface or merged module is changed. -/
set_option autoImplicit false
namespace AspisR1.NPH_R22Callbacks2
open Aeneas Aeneas.Std Result AspisR1.NPH_R22Installers

theorem and511_lt (u : Usize) : (u &&& 511#usize).val < 512 := by
  rw [UScalar.val_and]
  have h := Nat.and_le_right (n := u.val) (m := (511#usize).val)
  have h5 : (511#usize).val = 511 := by first | rfl | simp | scalar_tac
  omega

theorem table_value_eq (q : U32 × U32) :
    AspisR1QueryGeometryActual.fast_domain.table_value R17CurrentCM31Semantics.operations q =
      R17CurrentCM31Semantics.operations.new q.1 q.2 := by
  cases q; rfl

/-- fibre_point under the installed R17 CM31 operations (op15 body and line_node prefix). -/
theorem fibre_point_W (u : Usize) :
    (∃ p, AspisR1QueryGeometryActual.fast_domain.fibre_point R17CurrentCM31Semantics.operations u = ok p ∧
        W p.x ∧ W p.y) ∨
    (∃ i1, (u >>> 9#i32 : Result Usize) = ok i1 ∧ 512 ≤ i1.val) := by
  obtain ⟨i1, hs⟩ := AspisR1.NPH_R22QRawShift.fibre_shift_ok u
  by_cases hb : i1.val < 512
  · left
    have hi := and511_lt u
    have hA := R17ActualTableArrayIndexV1.tableA_index_entries (u &&& 511#usize) hi
    have cA := NEA_TableCanonical.readA (u &&& 511#usize) hi _ hA
    have hB := R17ActualTableArrayIndexV1.tableB_index_entries i1 hb
    have cB := NEA_TableCanonical.readB i1 hb _ hB
    obtain ⟨l, hl, wl1, wl2⟩ := R17_CM31_operations_new_W _ _ (Nat.le_of_lt cA.1) (Nat.le_of_lt cA.2)
    obtain ⟨r, hr, wr1, wr2⟩ := R17_CM31_operations_new_W _ _ (Nat.le_of_lt cB.1) (Nat.le_of_lt cB.2)
    obtain ⟨pt, hpt, wp1, wp2⟩ := R17_CM31_operations_mul_W l r wl1 wl2 wr1 wr2
    refine ⟨{ x := pt.a, y := pt.b }, ?_, wp1, wp2⟩
    simp only [AspisR1QueryGeometryActual.fast_domain.fibre_point, AspisR1QueryGeometryActual.domain.FibreIndex.get,
      lift, bind_tc_ok, hA, hs, hB, table_value_eq, hl, hr, hpt]
  · exact Or.inr ⟨i1, hs, by omega⟩

/-- op15: SAQ_Geometry.point. -/
theorem SAQ_Geometry_point_W (u : Usize) :
    (∃ p, SAQ_Geometry.point u = ok p ∧ W p.x ∧ W p.y) ∨
    (∃ i1, (u >>> 9#i32 : Result Usize) = ok i1 ∧ 512 ≤ i1.val) := by
  rcases fibre_point_W u with ⟨p, hp, wx, wy⟩ | h
  · exact Or.inl ⟨⟨p.x, p.y⟩, by simp only [SAQ_Geometry.point, hp, bind_tc_ok], wx, wy⟩
  · exact Or.inr h

/-- op14: SAQ_Geometry.line (line_node with the installed R17 M31 operations). -/
theorem SAQ_Geometry_line_W (u : Usize) :
    (∃ x, SAQ_Geometry.line u = ok x ∧ W x) ∨
    (∃ i1, (u >>> 9#i32 : Result Usize) = ok i1 ∧ 512 ≤ i1.val) := by
  rcases fibre_point_W u with ⟨p, hp, wx, _⟩ | h
  · obtain ⟨hmul, hdbl, hsub⟩ := R17_M31_operations_W
    obtain ⟨sq, hsq, wsq⟩ := hmul p.x p.x wx wx
    obtain ⟨m, hm, wm⟩ := hdbl sq wsq
    obtain ⟨z, hz, wz⟩ := hsub m 1#u32 wm (by unfold W; first | decide | simp | scalar_tac)
    exact Or.inl ⟨z, by simp only [SAQ_Geometry.line, R17FibrePointLineNodeActual.line_node, hp, hsq, hm, hz, bind_tc_ok], wz⟩
  · exact Or.inr h

/-- NFN_NEW_GeometryContextGeneric.replace installs sub/double; the M31-level W record is
preserved whenever the installed callbacks preserve W. -/
theorem NFN_replace_W {CE : Type} (o : Port3_NativeGeometryBody.Ops CE) (sub : U32 → U32 → Result U32)
    (double : U32 → Result U32) (ho : GeometryM31W o) (hs : Pres2 sub) (hd : Pres1 double) :
    GeometryM31W (NFN_NEW_GeometryContextGeneric.replace o sub double) :=
  ⟨ho.op7, hs, ho.op9, hd⟩

/-! ### conversion glue: limb-wise copies -/

theorem NNU_toQM_limbs (x : AspisR1CurrentWide.field.QM31) :
    (AspisR1.NNU_QueryFieldBase.toQM x).c0.a = x.c0.a ∧ (AspisR1.NNU_QueryFieldBase.toQM x).c0.b = x.c0.b ∧
    (AspisR1.NNU_QueryFieldBase.toQM x).c1.a = x.c1.a ∧ (AspisR1.NNU_QueryFieldBase.toQM x).c1.b = x.c1.b :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem CWBridge_toQM_limbs (x : AspisR1CurrentWide.field.QM31) :
    (AspisR1CurrentWide.Proof.toQM x).c0.a = x.c0.a ∧ (AspisR1CurrentWide.Proof.toQM x).c0.b = x.c0.b ∧
    (AspisR1CurrentWide.Proof.toQM x).c1.a = x.c1.a ∧ (AspisR1CurrentWide.Proof.toQM x).c1.b = x.c1.b :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem resultMap_ok {A B : Type} (f : A → B) (x : A) :
    AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20.resultMap f (ok x) = ok (f x) := rfl

theorem resultMap_ok_inv {A B : Type} (f : A → B) (r : Result A) (y : B)
    (h : AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20.resultMap f r = ok y) :
    ∃ x, r = ok x ∧ f x = y := by
  cases r with
  | ok x => exact ⟨x, rfl, Result.ok.inj h⟩
  | fail e => cases h
  | div => cases h

theorem genQToProbe_limbs (x : AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20.GenQ) :
    (AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20.genQToProbe x).c0.a = x.c0.a ∧
    (AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20.genQToProbe x).c0.b = x.c0.b ∧
    (AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20.genQToProbe x).c1.a = x.c1.a ∧
    (AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20.genQToProbe x).c1.b = x.c1.b :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem probeCToGen_limbs (x : AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20.ProbeC) :
    (AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20.probeCToGen x).a = x.a ∧
    (AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20.probeCToGen x).b = x.b :=
  ⟨rfl, rfl⟩

#print axioms and511_lt
#print axioms table_value_eq
#print axioms fibre_point_W
#print axioms SAQ_Geometry_point_W
#print axioms SAQ_Geometry_line_W
#print axioms NFN_replace_W
#print axioms NNU_toQM_limbs
#print axioms CWBridge_toQM_limbs
#print axioms resultMap_ok
#print axioms resultMap_ok_inv
#print axioms genQToProbe_limbs
#print axioms probeCToGen_limbs
end AspisR1.NPH_R22Callbacks2
