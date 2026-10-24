import S9CirclePointscanOuterSemanticsV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9CirclePointscanReadMeaningV1
open AspisR1S9FactorArrayEntryV1 AspisR1S9FactorTableSemanticsV1
open AspisR1S9CirclePointscanModelV1

theorem circleScan_point_read (before : Table) (z : Array Point 2#usize)
    (k : Usize) (point : Point) (hk : k.val<2)
    (hread : Array.index_usize z k=.ok point)
    (d i : Nat) (hd : d<5) :
    circleScanTable before z 2 (3+k.val) d i=circleRow point d i := by
  have hp : z.val[k.val]?=some point := by
    have he := accepted_index_eq_atN z k hk point hread
    rw [he]
    unfold atN
    exact List.getElem?_eq_getElem (by simpa [z.property] using hk)
  have hb : 3 ≤ 3+k.val ∧ 3+k.val<3+2 ∧ d<5 := by omega
  have he : 3+k.val-3=k.val := by omega
  simp only [circleScanTable,if_pos hb,pointRow,he,hp]

/-- Read-level statement-row frame, suitable for composing the preceding
statement phase without exposing the option-based source table model. -/
theorem circleScan_preserves_statement_meaning (before : Table)
    (z : Array Point 2#usize) (out : AspisR1S9ConstructorV3Loop2InnerCanonicalV1.Factors)
    (hm : Meaning out (circleScanTable before z 2))
    (k d i : Usize) (hk : k.val<3) (hd : d.val<5) (hi : i.val<4) :
    value out k d i (by omega) hd hi=before k.val d.val i.val := by
  exact (hm k d i (by omega) hd hi).trans
    (circleScan_statement_frame before z 2 k.val d.val i.val hk)

#print axioms circleScan_point_read
#print axioms circleScan_preserves_statement_meaning
end AspisR1S9CirclePointscanReadMeaningV1
