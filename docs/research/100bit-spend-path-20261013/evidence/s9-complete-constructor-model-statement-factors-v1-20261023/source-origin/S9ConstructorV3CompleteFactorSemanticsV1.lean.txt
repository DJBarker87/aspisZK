import S9ConstructorV3SourcePhasesV1
import S9ConstructorV3StatementProducerCanonicalV1
import S9StatementFactorOuterSemanticsV1
import S9CirclePointscanOuterSemanticsV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ConstructorV3CompleteFactorSemanticsV1
open AspisR1S9ActualWeightsNewBoxNewV3
open AspisR1S9ConstructorV3Loop2InnerCanonicalV1
abbrev Circles := AspisR1S9ConstructorV3SourcePhasesV1.Circles
open AspisR1S9ConstructorV3SuccessorCarryBodyCanonicalV1
open AspisR1S9ConstructorV3PointScanBodyCanonicalV1
open AspisR1S9FactorTableSemanticsV1
open AspisR1S9StatementFactorOuterSemanticsV1
open AspisR1S9CirclePointscanModelV1

/-- Every valid circle-factor row has the retained natural-circle formulas
at the exact point read from the same constructor input. -/
def CircleRows (z : Circles) (model : Table) : Prop :=
  ∀ (k d i : Usize) (hk : 3 ≤ k.val) (hk5 : k.val<5)
    (hd : d.val<5) (hi : i.val<4),
    model k.val d.val i.val = pointRow z (k.val-3) d.val i.val

/-- Complete accepted extracted constructor factor semantics. Canonical
actual inputs and this one source execution derive both phases' calls,
all 3 statement rows' D18 meanings, both circle rows' natural-basis meanings,
and exact stored points/extra/variant. No per-phase success or factor-meaning
contract remains an input to this theorem. Rust-cut normalization, allocation
and runtime/artifact correspondence are separate release obligations. -/
theorem constructor_success_complete_factor_semantics
    (variant : Variant) (alpha : Vector) (z : Circles) (w : Weights)
    (halpha : VectorCanonical alpha) (hz : PointsCanonical z)
    (hnew : weights_new variant alpha z = .ok (.Ok w)) :
    ∃ model : Table,
      Meaning w.factors model ∧ RowsPrefix w.points model 3 ∧ CircleRows z model ∧
      state_only_prefix.r0.statement_points alpha = .ok w.points ∧ w.variant=variant ∧
      ∃ (q8 q9 : Q), Array.index_usize alpha 8#usize=.ok q8 ∧
        Array.index_usize alpha 9#usize=.ok q9 ∧
        w.extra=Array.make 2#usize [q8,q9] := by
  obtain ⟨points,q8,q9,factors1,factors2,hpoints,h8,h9,hphase1,hphase2,hw⟩ :=
    AspisR1S9ConstructorV3SourcePhasesV1.constructor_success_source_phases variant alpha z w hnew
  have hpointsCan :=
    AspisR1S9ConstructorV3StatementProducerCanonicalV1.statement_points_success_canonical
      alpha points halpha hpoints
  obtain ⟨statementModel,hm1,hstatement,hframe⟩ :=
    statement_outer_success_actual_table points
      AspisR1S9ConstructorV3InitialFactorsCanonicalV1.initialFactors factors1 hpointsCan hphase1
  have hm2 := AspisR1S9CirclePointscanOuterSemanticsV1.circle_outer_success_meaning
    statementModel z factors1 factors2 hz hm1 hphase2
  let finalModel := circleScanTable statementModel z 2
  have hstatement2 : RowsPrefix points finalModel 3 := by
    intro k d i hk hd hi hsmall
    change circleScanTable statementModel z 2 k.val d.val i.val = _
    rw [circleScan_statement_frame statementModel z 2 k.val d.val i.val hk]
    exact hstatement k d i hk hd hi hsmall
  have hcircle : CircleRows z finalModel := by
    intro k d i hk hk5 hd hi
    have hcond : 3 ≤ k.val ∧ k.val<3+2 ∧ d.val<5 := by omega
    change (if 3 ≤ k.val ∧ k.val<3+2 ∧ d.val<5 then
      pointRow z (k.val-3) d.val i.val else statementModel k.val d.val i.val) = _
    rw [if_pos hcond]
  rw [hw]
  exact ⟨finalModel,hm2,hstatement2,hcircle,hpoints,rfl,q8,q9,h8,h9,rfl⟩

#print axioms constructor_success_complete_factor_semantics
end AspisR1S9ConstructorV3CompleteFactorSemanticsV1
