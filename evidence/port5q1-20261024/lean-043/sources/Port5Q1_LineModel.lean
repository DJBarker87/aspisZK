import S7OwnedP6StoredNode
import R1QueryResidualBridge
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port5Q1_LineModel
open AspisCircleGroupOrder
open AspisV5FriDegreeThreeCorrelatedAgreement
open AspisV5ComponentCConcreteFoldLinearity AspisV5FriConcreteEncoderCommutation
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod P) F]
attribute [local irreducible] SecondFoldRestoration.channels SecondFoldRestoration.transform

theorem fold (alpha : F) (V : Fin 262144 → F) (u : Fin 65536) :
    FoldRuntimeAlgebra.lineWithInverses alpha
      (FoldGeometryBridge.lx u)⁻¹ (FoldGeometryBridge.ly u)⁻¹ (FoldGeometryBridge.lz u)⁻¹
      (fun j => V (AspisR1.childIndex u j))=
    curveValue (SecondFoldRestoration.channels V) alpha u := by
  have hx : FoldGeometryBridge.lx (K:=F) u=SecondFoldRestoration.x0 u := by
    simp only [FoldGeometryBridge.lx,FoldStoredGeometry.x18_eq_stored,SecondFoldRestoration.x0]
  have hy : FoldGeometryBridge.ly (K:=F) u= -SecondFoldRestoration.x1 u := by
    simp only [FoldGeometryBridge.ly,FoldStoredGeometry.runtime_y,map_neg,
      FoldStoredGeometry.x18_eq_stored,SecondFoldRestoration.x1]
  have hz : FoldGeometryBridge.lz (K:=F) u=SecondFoldRestoration.x2 u :=
    FoldGeometryBridge.z_eq_model u
  have source := S7OwnedP6StoredNode.inverse_line_fold_to_model alpha u
    (fun j => V (AspisR1.childIndex u j)) AspisWide.InitialEncoder.two_ne_zero
    (by rw [hx]; exact SecondFoldRestoration.x0_ne_zero u)
    (by rw [hy]; exact neg_ne_zero.mpr (SecondFoldRestoration.x1_ne_zero u))
    (by rw [hz]; exact SecondFoldRestoration.x2_ne_zero u)
  rw [source]
  change lineFoldValue alpha (SecondFoldRestoration.inverse0 u)
    (SecondFoldRestoration.inverse1 u) (SecondFoldRestoration.inverse2 u) _ = _
  have products := SecondFoldRestoration.inverse_products (K:=F) u
  rw [lineFoldValue_eq_coefficientFoldValue_decode alpha
    (SecondFoldRestoration.x0 u) (SecondFoldRestoration.x1 u) (SecondFoldRestoration.x2 u)
    (SecondFoldRestoration.inverse0 u) (SecondFoldRestoration.inverse1 u) (SecondFoldRestoration.inverse2 u)
    products.1 products.2.1 products.2.2]
  unfold curveValue AspisV5FunctionalBatching.batchedDiscrepancy coefficientFoldValue
    SecondFoldRestoration.channels SecondFoldRestoration.transform
  ring

#print axioms fold
end AspisR1.Port5Q1_LineModel
end
