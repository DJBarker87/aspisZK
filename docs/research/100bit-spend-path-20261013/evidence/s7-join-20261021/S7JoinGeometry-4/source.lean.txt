import S7OwnedP6StoredNode
import R1SecondFoldRestoration

/-! Stored geometry at every query, with nonzero line denominators proved
from the released domain. Literal table certification remains explicit. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.S7JoinGeometry
open AspisCircleGroupOrder AspisV7ExactOneFoldDomains
open FoldGeometryBridge FoldStoredGeometry
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] [Algebra (ZMod P) K]

theorem line_nonzero (u : Fin 65536) :
    lx (K:=K) u≠0 ∧ ly (K:=K) u≠0 ∧ lz (K:=K) u≠0 := by
  have hx : lx (K:=K) u = SecondFoldRestoration.x0 u := by
    simp only [lx,x18_eq_stored,SecondFoldRestoration.x0]
  have hy : ly (K:=K) u = -SecondFoldRestoration.x1 u := by
    unfold ly
    rw [runtime_y,map_neg]
    simp only [x18_eq_stored,SecondFoldRestoration.x1]
  have hz : lz (K:=K) u = SecondFoldRestoration.x2 u := z_eq_model u
  rw [hx,hy,hz]
  exact ⟨SecondFoldRestoration.x0_ne_zero u,
    neg_ne_zero.mpr (SecondFoldRestoration.x1_ne_zero u),SecondFoldRestoration.x2_ne_zero u⟩

/-- No zero-test hypothesis is required for the actual stored line geometry. -/
theorem line_total_join (alpha : K) (u : Fin 65536) (v : Fin 4 → K) :
    FoldRuntimeAlgebra.lineWithInverses alpha (lx u)⁻¹ (ly u)⁻¹ (lz u)⁻¹ v =
      AspisV5ComponentCConcreteFoldLinearity.lineFoldValue alpha
        (SecondFoldRestoration.inverse0 u) (SecondFoldRestoration.inverse1 u)
        (SecondFoldRestoration.inverse2 u) v := by
  have hn := line_nonzero (K:=K) u
  exact S7OwnedP6StoredNode.inverse_line_fold_to_model alpha u v
    AspisWide.InitialEncoder.two_ne_zero hn.1 hn.2.1 hn.2.2

/-- The extra source T2 is the precise node used by dV's basis, for every query. -/
theorem query_node (q : Fin 22 → Fin 262144) (j : Fin 22) :
    2*(lz (K:=K) (parentIndex (q j)))^2-1 =
      algebraMap (ZMod P) K (AspisV5FriReleasedLineGeometry.storedLine16X (parentIndex (q j))) :=
  S7OwnedP6StoredNode.extra_t2_is_final_node _

#print axioms line_nonzero
#print axioms line_total_join
#print axioms query_node
end AspisR1.S7JoinGeometry
